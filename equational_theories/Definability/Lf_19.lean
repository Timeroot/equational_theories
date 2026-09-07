import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq12 X0 X1
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq49 X1 (k X1 X1)
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq51 X1 (k X1 X1)
       have r₂ := eq10 (k X1 X1) X1
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

/-- `x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq55 X1 X0
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq59 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq59
  have eq160 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq165 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq160 X1 X0
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq160 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq160 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq160
  have eq186 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq165 (σ X1) (σ X0)
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
       have i₂ := eq165 X1 X0
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

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq69 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq72 X0 X0
       have r₂ := eq10 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq72 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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

/-- `x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq12 X0 X1
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq58 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq97 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq97 X0 X0
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq97 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq97
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq101 (σ X0) (σ X1)
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
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq124
    | exact resolve eq124 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq124
  have eq1145 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1167 : False := by grind
  exact eq1167

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X0)
       have r₂ := eq38 X0 X0
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq76 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq201 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
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
  have eq208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq216 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq201
    | (have j0 := eq201 X0 X1
       grind)
    | exact resolve eq201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq201
  have eq790 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq216
    | exact resolve eq216 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq950 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq790 (τ X1) X0
       grind)
    | exact superpose eq790 eq16
    | (have j1 := eq790 (τ X1) X0
       grind)
    | exact resolve eq16 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq1129 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq208
       have i₂ := eq790 y x
       grind)
    | exact superpose eq790 eq208
    | (have j1 := eq790 (σ y) (σ x)
       grind)
    | exact resolve eq208 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq790
  have eq1132 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1129
  have eq1135 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq14
    | exact resolve eq14 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1132
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1132
       grind)
    | exact resolve eq11 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1138 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1136
  have eq1140 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1138
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1138
    | exact resolve eq1138 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1845 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq950
    | exact resolve eq950 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1902 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
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
  have eq13582 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq1140
       grind)
    | exact superpose eq1140 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq1140
       grind)
    | exact resolve eq10 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq13583 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq13582
  have eq13584 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13583
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq13583
    | exact resolve eq13583 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13583
  have eq42030 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1132
       have i₂ := eq13584
       grind)
    | exact superpose eq13584 eq1132
    | exact resolve eq1132 eq13584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq13584
  have eq42049 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq42030
  have eq42367 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1902 y x
       have i₂ := eq42049
       grind)
    | exact superpose eq42049 eq1902
    | (have j0 := eq1902 y x
       grind)
    | exact resolve eq1902 eq42049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902 eq42049
  have eq42454 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq42367
  have eq42481 : x = (M.op x y) := by
    first
    | (have r₁ := eq42454
       have r₂ := eq1135
       grind)
    | exact resolve eq42454 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq42454
  have eq42775 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq42481
       grind)
    | exact superpose eq42481 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq42481
       grind)
    | exact resolve eq11 eq42481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42776 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq42775
  have eq43371 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq42776
       grind)
    | exact superpose eq42776 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq42776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42776
  have eq43433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq43371
  have eq44054 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43433
       grind)
    | exact superpose eq43433 eq14
    | exact resolve eq14 eq43433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43433
  have eq44062 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44054
       have i₂ := eq42481
       grind)
    | exact superpose eq42481 eq44054
    | exact resolve eq44054 eq42481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44054
  have eq44063 : x = (M.op y x) := by grind
  clear eq44062
  have eq44378 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq44063
       grind)
    | exact superpose eq44063 eq10
    | (have j0 := eq10 x y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq44063
       grind)
    | exact resolve eq10 eq44063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44063
  have eq44386 : (M.op x y) = (k x y) := by grind
  clear eq44378
  have eq44388 : x = (k x y) := by
    first
    | (have i₁ := eq44386
       have i₂ := eq42481
       grind)
    | exact superpose eq42481 eq44386
    | exact resolve eq44386 eq42481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44386
  have eq44696 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq44388
       grind)
    | exact superpose eq44388 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq44388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq44388
  have eq44756 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44696
  have eq45042 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44756
       grind)
    | exact superpose eq44756 eq14
    | exact resolve eq14 eq44756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44756
  have eq45050 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq45042
       have i₂ := eq42481
       grind)
    | exact superpose eq42481 eq45042
    | exact resolve eq45042 eq42481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42481 eq45042
  have eq45051 : False := by grind
  exact eq45051

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq75 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq203 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
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
  have eq206 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq14
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq14 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq212 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq203
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq789 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq212
    | exact resolve eq212 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq874 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq789 (τ X0) X1
       grind)
    | exact superpose eq789 eq15
    | (have j1 := eq789 (τ X0) X1
       grind)
    | exact resolve eq15 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq206
       have i₂ := eq789 x y
       grind)
    | exact superpose eq789 eq206
    | (have j1 := eq789 (σ x) (σ y)
       grind)
    | exact resolve eq206 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq789
  have eq964 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq961
  have eq966 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq14
    | exact resolve eq14 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq964
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq964
       grind)
    | exact resolve eq11 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq964
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq964
       grind)
    | exact resolve eq10 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq969 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq968
  have eq970 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq967
  have eq971 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq969
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq969
    | exact resolve eq969 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq972 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq970
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq970
    | exact resolve eq970 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq2413 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq874 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq874
    | exact resolve eq874 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq2466 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
  have eq14322 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
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
  have eq14327 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq14322
  have eq14621 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq14327
       grind)
    | exact superpose eq14327 eq8
    | exact resolve eq8 eq14327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14327
  have eq14697 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14621
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq14621
    | exact resolve eq14621 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14621
  have eq14931 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2466 x y
       have i₂ := eq14697
       grind)
    | exact superpose eq14697 eq2466
    | (have j0 := eq2466 x y
       grind)
    | exact resolve eq2466 eq14697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14697
  have eq14988 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq14931
  have eq15016 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14988
       have r₂ := eq966
       grind)
    | exact resolve eq14988 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq14988
  have eq15303 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq214 y x
       have i₂ := eq15016
       grind)
    | exact superpose eq15016 eq214
    | (have j0 := eq214 y x
       grind)
    | exact resolve eq214 eq15016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq15016
  have eq15339 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq15303
  have eq16773 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15339
       grind)
    | exact superpose eq15339 eq14
    | exact resolve eq14 eq15339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339
  have eq16796 : y = (M.op x y) := by
    first
    | (have j1 := eq2466 x y
       grind)
    | (have r₁ := eq16773
       have r₂ := eq2466 x y
       grind)
    | exact resolve eq16773 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq16773
  have eq16993 : y ≠ y ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16796
       grind)
    | exact superpose eq16796 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq16796
       grind)
    | exact resolve eq11 eq16796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16996 : y = (k x y) ∨ x = (M.op y x) := by grind
  clear eq16993
  have eq17483 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq16996
       grind)
    | exact superpose eq16996 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq16996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16996
  have eq17521 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq17483
  have eq18454 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17521
       grind)
    | exact superpose eq17521 eq14
    | exact resolve eq14 eq17521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17521
  have eq18461 : (σ y) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18454
       have i₂ := eq16796
       grind)
    | exact superpose eq16796 eq18454
    | exact resolve eq18454 eq16796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18454
  have eq18462 : x = (M.op y x) := by grind
  clear eq18461
  have eq18729 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq18462
       grind)
    | exact superpose eq18462 eq10
    | (have j0 := eq10 x y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq18462
       grind)
    | exact resolve eq10 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq18730 : (M.op x y) = (k x y) := by grind
  clear eq18729
  have eq18732 : y = (k x y) := by
    first
    | (have i₁ := eq18730
       have i₂ := eq16796
       grind)
    | exact superpose eq16796 eq18730
    | exact resolve eq18730 eq16796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18730
  have eq19007 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq18732
       grind)
    | exact superpose eq18732 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq18732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq18732
  have eq19043 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19007
  have eq19630 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19043
       grind)
    | exact superpose eq19043 eq14
    | exact resolve eq14 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19043
  have eq19636 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq19630
       have i₂ := eq16796
       grind)
    | exact superpose eq16796 eq19630
    | exact resolve eq19630 eq16796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16796 eq19630
  have eq19637 : False := by grind
  exact eq19637

/-- `x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X1 X0
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq51 X0 (k X0 X0)
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq49 X1 (k X1 X1)
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq52 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq52 X1 (k X1 X1)
       have r₂ := eq10 (k X1 X1) X1
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq53 X0 (M.op X1 (M.op X0 X0))
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
       have r₂ := eq54 X0 (k X1 X0)
       grind)
    | exact resolve eq59 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq59
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq122 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X0
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
    | (have r₁ := eq122 X1 X1
       have r₂ := eq67 X1 X1
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
  have eq1052 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1075 : False := by grind
  exact eq1075
