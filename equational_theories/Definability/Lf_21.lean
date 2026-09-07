import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq49 (k X0 X0) X0
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq51 (k X0 X0) X0
       have r₂ := eq10 X0 (k X0 X0)
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
  have eq1143 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1165 : False := by grind
  exact eq1165

/-- `x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq38 X1 X0
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
  have eq75 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq200 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
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
  have eq206 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq209 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq81 X1 X0
       grind)
    | exact superpose eq81 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq10 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq211 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq213 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq200
  have eq214 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq789 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq858 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq789 (τ X1) X0
       grind)
    | exact superpose eq789 eq16
    | (have j1 := eq789 (τ X1) X0
       grind)
    | exact resolve eq16 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
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
  have eq967 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq968 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq969 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq968
  have eq970 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq967
  have eq971 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = (M.op x y) := by
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
  have eq972 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
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
  have eq2413 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq858 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq858
    | exact resolve eq858 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq2466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2413 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2413
    | (have j0 := eq2413 X0 X1
       grind)
    | exact resolve eq2413 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq14330 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
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
  have eq14335 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq14330
  have eq14617 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq14335
       grind)
    | exact superpose eq14335 eq8
    | exact resolve eq8 eq14335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14335
  have eq14693 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14617
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq14617
    | exact resolve eq14617 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14617
  have eq14926 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2466 y x
       have i₂ := eq14693
       grind)
    | exact superpose eq14693 eq2466
    | (have j0 := eq2466 y x
       grind)
    | exact resolve eq2466 eq14693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14693
  have eq14983 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq14926
  have eq15011 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14983
       have r₂ := eq966
       grind)
    | exact resolve eq14983 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq14983
  have eq15310 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq214 y x
       have i₂ := eq15011
       grind)
    | exact superpose eq15011 eq214
    | (have j0 := eq214 y x
       grind)
    | exact resolve eq214 eq15011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq15011
  have eq15346 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq15310
  have eq16781 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15346
       grind)
    | exact superpose eq15346 eq14
    | exact resolve eq14 eq15346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15346
  have eq16804 : x = (M.op x y) := by
    first
    | (have j1 := eq2466 y x
       grind)
    | (have r₁ := eq16781
       have r₂ := eq2466 y x
       grind)
    | exact resolve eq16781 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq16781
  have eq17001 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16804
       grind)
    | exact superpose eq16804 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq16804
       grind)
    | exact resolve eq11 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17004 : x = (k x y) ∨ y = (M.op y x) := by grind
  clear eq17001
  have eq17491 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq17004
       grind)
    | exact superpose eq17004 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq17004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17004
  have eq17529 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq17491
  have eq18462 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17529
       grind)
    | exact superpose eq17529 eq14
    | exact resolve eq14 eq17529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17529
  have eq18469 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18462
       have i₂ := eq16804
       grind)
    | exact superpose eq16804 eq18462
    | exact resolve eq18462 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq18470 : y = (M.op y x) := by grind
  clear eq18469
  have eq18743 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq18470
       grind)
    | exact superpose eq18470 eq10
    | (have j0 := eq10 x y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq18470
       grind)
    | exact resolve eq10 eq18470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18470
  have eq18744 : (M.op x y) = (k x y) := by grind
  clear eq18743
  have eq18746 : x = (k x y) := by
    first
    | (have i₁ := eq18744
       have i₂ := eq16804
       grind)
    | exact superpose eq16804 eq18744
    | exact resolve eq18744 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18744
  have eq19027 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq18746
       grind)
    | exact superpose eq18746 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq18746
  have eq19063 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19027
  have eq19638 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19063
       grind)
    | exact superpose eq19063 eq14
    | exact resolve eq14 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19063
  have eq19644 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq19638
       have i₂ := eq16804
       grind)
    | exact superpose eq16804 eq19638
    | exact resolve eq19638 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16804 eq19638
  have eq19645 : False := by grind
  exact eq19645

/-- `x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
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
  have eq76 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq204 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
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
  have eq208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq215 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq204
  have eq790 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq966 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq790 (τ X0) X1
       grind)
    | exact superpose eq790 eq15
    | (have j1 := eq790 (τ X0) X1
       grind)
    | exact resolve eq15 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
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
  have eq1136 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq1138 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1136
  have eq1140 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
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
  have eq1847 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq966 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq966
    | exact resolve eq966 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1904 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1847 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1847
    | (have j0 := eq1847 X0 X1
       grind)
    | exact resolve eq1847 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq13597 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
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
  have eq13598 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq13597
  have eq13599 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13598
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq13598
    | exact resolve eq13598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13598
  have eq41864 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1132
       have i₂ := eq13599
       grind)
    | exact superpose eq13599 eq1132
    | exact resolve eq1132 eq13599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq13599
  have eq41883 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq41864
  have eq42196 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1904 x y
       have i₂ := eq41883
       grind)
    | exact superpose eq41883 eq1904
    | (have j0 := eq1904 x y
       grind)
    | exact resolve eq1904 eq41883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904 eq41883
  have eq42283 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq42196
  have eq42310 : y = (M.op x y) := by
    first
    | (have r₁ := eq42283
       have r₂ := eq1135
       grind)
    | exact resolve eq42283 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq42283
  have eq42603 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq42310
       grind)
    | exact superpose eq42310 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq42310
       grind)
    | exact resolve eq11 eq42310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42604 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq42603
  have eq43210 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq42604
       grind)
    | exact superpose eq42604 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq42604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42604
  have eq43272 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq43210
  have eq43879 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43272
       grind)
    | exact superpose eq43272 eq14
    | exact resolve eq14 eq43272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43272
  have eq43887 : (σ y) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq43879
       have i₂ := eq42310
       grind)
    | exact superpose eq42310 eq43879
    | exact resolve eq43879 eq42310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43879
  have eq43888 : y = (M.op y x) := by grind
  clear eq43887
  have eq44203 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq43888
       grind)
    | exact superpose eq43888 eq10
    | (have j0 := eq10 x y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq43888
       grind)
    | exact resolve eq10 eq43888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43888
  have eq44211 : (M.op x y) = (k x y) := by grind
  clear eq44203
  have eq44213 : y = (k x y) := by
    first
    | (have i₁ := eq44211
       have i₂ := eq42310
       grind)
    | exact superpose eq42310 eq44211
    | exact resolve eq44211 eq42310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44211
  have eq44520 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq44213
       grind)
    | exact superpose eq44213 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq44213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq44213
  have eq44580 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq44520
  have eq44866 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44580
       grind)
    | exact superpose eq44580 eq14
    | exact resolve eq14 eq44580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44580
  have eq44874 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq44866
       have i₂ := eq42310
       grind)
    | exact superpose eq42310 eq44866
    | exact resolve eq44866 eq42310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42310 eq44866
  have eq44875 : False := by grind
  exact eq44875

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq54 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq64 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq160 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X1 X0
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
    | (have r₁ := eq160 X1 X1
       have r₂ := eq63 X1 X1
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

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq294 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq301 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq306 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq307 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq306
    | (have j0 := eq306 X0 X1
       grind)
    | exact resolve eq306 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq308 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
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
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X0
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
  have eq354 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq361 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq366 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq367 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq368 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
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
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X0
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
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq414
  have eq2756 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq415
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq415
       grind)
    | exact resolve eq11 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2758 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq415
  have eq2759 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2756
  have eq2760 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2759
       have r₂ := eq2758
       grind)
    | exact resolve eq2759 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758 eq2759
  have eq2762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2760
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2760
    | exact resolve eq2760 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq19252 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq2762
       grind)
    | exact superpose eq2762 eq10
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq2762
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq2762
       grind)
    | exact resolve eq10 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq19253 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19252
  have eq19255 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19253
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq19253
    | exact resolve eq19253 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253
  have eq19725 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq19255
       grind)
    | exact superpose eq19255 eq8
    | exact resolve eq8 eq19255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19255
  have eq19872 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19725
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq19725
    | exact resolve eq19725 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19725
  have eq19875 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 y x
       grind)
    | (have r₁ := eq19872
       have r₂ := eq309 y x
       grind)
    | exact resolve eq19872 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq19872
  have eq20115 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq19875
       grind)
    | exact superpose eq19875 eq8
    | exact resolve eq8 eq19875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19875
  have eq20262 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20115
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq20115
    | exact resolve eq20115 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20115
  have eq20263 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq369 y x
       grind)
    | (have r₁ := eq20262
       have r₂ := eq369 y x
       grind)
    | exact resolve eq20262 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq20262
  have eq20494 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20263
       grind)
    | exact superpose eq20263 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq20263
       grind)
    | exact resolve eq11 eq20263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20496 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq20497 : x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq20494
  have eq20498 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20497
       have r₂ := eq20496
       grind)
    | exact resolve eq20497 eq20496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20497
  have eq21020 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq20498
       grind)
    | exact superpose eq20498 eq64
    | (have j0 := eq64 x y
       grind)
    | exact resolve eq64 eq20498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq21065 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21020
  have eq26259 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21065
       grind)
    | exact superpose eq21065 eq14
    | exact resolve eq14 eq21065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21065
  have eq26937 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26259
       have i₂ := eq20263
       grind)
    | exact superpose eq20263 eq26259
    | exact resolve eq26259 eq20263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26259
  have eq26940 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26937
  have eq26941 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26940
       have r₂ := eq20496
       grind)
    | exact resolve eq26940 eq20496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26940
  have eq27364 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26941
       grind)
    | exact superpose eq26941 eq14
    | exact resolve eq14 eq26941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27365 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq26941
       grind)
    | exact superpose eq26941 eq10
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq26941
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq26941
       grind)
    | exact resolve eq10 eq26941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26941
  have eq27366 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27365
  have eq27369 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
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
  have eq27743 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27364
       have i₂ := eq20263
       grind)
    | exact superpose eq20263 eq27364
    | exact resolve eq27364 eq20263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20263 eq27364
  have eq27747 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27743
       have r₂ := eq20496
       grind)
    | exact resolve eq27743 eq20496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20496 eq27743
  have eq28440 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27369
       have i₂ := eq20498
       grind)
    | exact superpose eq20498 eq27369
    | exact resolve eq27369 eq20498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20498 eq27369
  have eq28592 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28440
  have eq28651 : x = (M.op x y) := by
    first
    | (have r₁ := eq28592
       have r₂ := eq27747
       grind)
    | exact resolve eq28592 eq27747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27747 eq28592
  have eq28980 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq28651
       grind)
    | exact superpose eq28651 eq10
    | (have r₁ := eq10 y x
       have r₂ := eq28651
       grind)
    | exact resolve eq10 eq28651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28981 : x = (k y x) := by grind
  clear eq28980
  have eq29368 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 x y
       have i₂ := eq28981
       grind)
    | exact superpose eq28981 eq65
    | (have j0 := eq65 x y
       grind)
    | exact resolve eq65 eq28981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq29394 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29368
  have eq33595 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq29394
       grind)
    | exact superpose eq29394 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq29394
       grind)
    | exact resolve eq11 eq29394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33597 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29394
  have eq33598 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33595
  have eq33599 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33598
       have r₂ := eq33597
       grind)
    | exact resolve eq33598 eq33597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33598
  have eq33602 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33599
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq33599
    | exact resolve eq33599 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33599
  have eq33604 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33602
       have i₂ := eq28981
       grind)
    | exact superpose eq28981 eq33602
    | exact resolve eq33602 eq28981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28981 eq33602
  have eq33605 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33604
       have r₂ := eq33597
       grind)
    | exact resolve eq33604 eq33597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33597 eq33604
  have eq33981 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33605
       grind)
    | exact superpose eq33605 eq14
    | exact resolve eq14 eq33605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33605
  have eq33985 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq33981
       have i₂ := eq28651
       grind)
    | exact superpose eq28651 eq33981
    | exact resolve eq33981 eq28651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28651 eq33981
  have eq33986 : False := by grind
  exact eq33986

/-- `x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq42 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq294 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq301 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq306 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq307 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq306
    | (have j0 := eq306 X0 X1
       grind)
    | exact resolve eq306 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq308 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
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
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X0
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
  have eq354 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq361 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq366 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq367 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq368 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
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
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X0
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
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq414
  have eq2224 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq415
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq415
       grind)
    | exact resolve eq11 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2226 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq415
  have eq2227 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2224
  have eq2228 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2227
       have r₂ := eq2226
       grind)
    | exact resolve eq2227 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226 eq2227
  have eq2230 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2228
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2228
    | exact resolve eq2228 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq17918 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq2230
       grind)
    | exact superpose eq2230 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq2230
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq2230
       grind)
    | exact resolve eq10 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq17919 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17918
  have eq17922 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17919
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq17919
    | exact resolve eq17919 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17919
  have eq18349 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq18496 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18349
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq18349
    | exact resolve eq18349 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18349
  have eq18499 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 y x
       grind)
    | (have r₁ := eq18496
       have r₂ := eq309 y x
       grind)
    | exact resolve eq18496 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq18496
  have eq18695 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq18499
       grind)
    | exact superpose eq18499 eq8
    | exact resolve eq8 eq18499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18499
  have eq18844 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18695
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq18695
    | exact resolve eq18695 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18695
  have eq18845 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq369 y x
       grind)
    | (have r₁ := eq18844
       have r₂ := eq369 y x
       grind)
    | exact resolve eq18844 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq18844
  have eq19032 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18845
       grind)
    | exact superpose eq18845 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq18845
       grind)
    | exact resolve eq11 eq18845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19034 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19035 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq19032
  have eq19036 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19035
       have r₂ := eq19034
       grind)
    | exact resolve eq19035 eq19034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19035
  have eq19423 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43 x y
       have i₂ := eq19036
       grind)
    | exact superpose eq19036 eq43
    | (have j0 := eq43 x y
       grind)
    | exact resolve eq43 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq19467 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19423
  have eq56818 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19467
       grind)
    | exact superpose eq19467 eq14
    | exact resolve eq14 eq19467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19467
  have eq56903 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56818
       have i₂ := eq18845
       grind)
    | exact superpose eq18845 eq56818
    | exact resolve eq56818 eq18845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56818
  have eq56906 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq56903
  have eq56907 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq56906
       have r₂ := eq19034
       grind)
    | exact resolve eq56906 eq19034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56906
  have eq56944 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56907
       grind)
    | exact superpose eq56907 eq14
    | exact resolve eq14 eq56907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56945 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq56907
       grind)
    | exact superpose eq56907 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq56907
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq56907
       grind)
    | exact resolve eq10 eq56907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56907
  have eq56946 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq56945
  have eq56949 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56946
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq56946
    | exact resolve eq56946 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56946
  have eq56988 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56944
       have i₂ := eq18845
       grind)
    | exact superpose eq18845 eq56944
    | exact resolve eq56944 eq18845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18845 eq56944
  have eq56992 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq56988
       have r₂ := eq19034
       grind)
    | exact resolve eq56988 eq19034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19034 eq56988
  have eq57044 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56949
       have i₂ := eq19036
       grind)
    | exact superpose eq19036 eq56949
    | exact resolve eq56949 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq57080 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq56949
       grind)
    | exact superpose eq56949 eq8
    | exact resolve eq8 eq56949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56949
  have eq57167 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq57044
  have eq57224 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57080
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq57080
    | exact resolve eq57080 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57080
  have eq57251 : x = (M.op x y) := by
    first
    | (have r₁ := eq57167
       have r₂ := eq56992
       grind)
    | exact resolve eq57167 eq56992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56992 eq57167
  have eq57252 : y = (k y x) := by
    first
    | (have j1 := eq10 y x
       grind)
    | (have r₁ := eq57224
       have r₂ := eq10 y x
       grind)
    | exact resolve eq57224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57224
  have eq57333 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42 x y
       have i₂ := eq57252
       grind)
    | exact superpose eq57252 eq42
    | (have j0 := eq42 x y
       grind)
    | exact resolve eq42 eq57252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq57372 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57333
  have eq58860 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq57372
       grind)
    | exact superpose eq57372 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq57372
       grind)
    | exact resolve eq11 eq57372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58862 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57372
  have eq58863 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58860
  have eq58864 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq58863
       have r₂ := eq58862
       grind)
    | exact resolve eq58863 eq58862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58863
  have eq58867 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58864
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq58864
    | exact resolve eq58864 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58864
  have eq58869 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58867
       have i₂ := eq57252
       grind)
    | exact superpose eq57252 eq58867
    | exact resolve eq58867 eq57252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57252 eq58867
  have eq58870 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq58869
       have r₂ := eq58862
       grind)
    | exact resolve eq58869 eq58862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58862 eq58869
  have eq58912 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58870
       grind)
    | exact superpose eq58870 eq14
    | exact resolve eq14 eq58870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58870
  have eq58916 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq58912
       have i₂ := eq57251
       grind)
    | exact superpose eq57251 eq58912
    | exact resolve eq58912 eq57251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57251 eq58912
  have eq58917 : False := by grind
  exact eq58917

/-- `x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
    | (have i₁ := eq108 (τ X0) X1
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
  have eq8938 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq9013 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq8938
  have eq9034 : x = (M.op x x) := by
    first
    | (have r₁ := eq9013
       have r₂ := eq8647
       grind)
    | exact resolve eq9013 eq8647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8647 eq9013
  have eq9136 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq9034
       grind)
    | exact superpose eq9034 eq10
    | (have r₁ := eq10 x x
       have r₂ := eq9034
       grind)
    | exact resolve eq10 eq9034
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
       have i₂ := eq9034
       grind)
    | exact superpose eq9034 eq9761
    | exact resolve eq9761 eq9034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9034 eq9761
  have eq9766 : False := by grind
  exact eq9766

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq98 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq100 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq457 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq48
    | exact resolve eq48 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq13 X0 X1
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
  have eq3567 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
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
  have eq3568 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3567
  have eq3570 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
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
  have eq6063 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
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
  have eq6109 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6063
  have eq6133 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6109
       have r₂ := eq3566
       grind)
    | exact resolve eq6109 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566 eq6109
  have eq6252 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq6133
       grind)
    | exact superpose eq6133 eq10
    | (have r₁ := eq10 y x
       have r₂ := eq6133
       grind)
    | exact resolve eq10 eq6133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6253 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6252
  have eq6419 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
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
  have eq6422 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6419
  have eq6423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6422
  have eq6592 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq6423
       grind)
    | exact superpose eq6423 eq14
    | exact resolve eq14 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6817 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6592
       have i₂ := eq6133
       grind)
    | exact superpose eq6133 eq6592
    | exact resolve eq6592 eq6133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6133 eq6592
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
