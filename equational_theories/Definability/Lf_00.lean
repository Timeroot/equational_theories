import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq64 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq211 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq218 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq211 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq211 X0 X0
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq211 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq211
  have eq243 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq218 (σ X1) (σ X0)
       grind)
    | exact superpose eq218 eq13
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq218 X1 X0
       grind)
    | exact superpose eq218 eq243
    | exact resolve eq243 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq243
  have eq1296 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq250 x y
       grind)
    | exact superpose eq250 eq14
    | (have r₁ := eq14
       have r₂ := eq250 x y
       grind)
    | exact resolve eq14 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1328 : False := by grind
  exact eq1328

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq54 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq11 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq213 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq220 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq213
    | (have j0 := eq213 X0 X1
       grind)
    | exact resolve eq213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq221 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq240 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq221
    | (have j0 := eq221 X0 X1
       grind)
    | exact resolve eq221 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq240 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq703 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq241 X0 X1
       grind)
    | exact resolve eq10 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq716 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq703 X0 X1
       grind)
    | (have r₁ := eq703 X0 X1
       have r₂ := eq26 X0
       grind)
    | exact resolve eq703 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq738 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq716
  have eq751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq738 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq738
    | (have j0 := eq738 X0 X1
       grind)
    | exact resolve eq738 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq758 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq751 X0 X1
       have j1 := eq713 X0 X1
       grind)
    | (have r₁ := eq751 X0 X1
       have r₂ := eq713 X0 X1
       grind)
    | exact resolve eq751 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq751
  have eq762 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq758 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq758
    | exact resolve eq758 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq758 x y
       grind)
    | exact superpose eq758 eq14
    | exact resolve eq14 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq1099 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq762 X0 (τ X1)
       grind)
    | exact superpose eq762 eq16
    | exact resolve eq16 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq762
  have eq1137 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1099 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1099
    | exact resolve eq1099 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1154 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1137 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1137
    | exact resolve eq1137 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1285 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq784
       have i₂ := eq1154 x y
       grind)
    | exact superpose eq1154 eq784
    | exact resolve eq784 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1154
  have eq1286 : False := by grind
  exact eq1286

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
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
  have eq156 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq11
    | (have j1 := eq55 X0 X1
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
  have eq157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X0)
       have r₂ := eq55 X0 X0
       grind)
    | (have r₁ := eq10 (σ X1) (σ X1)
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq10 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq180 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq157 X0 X0
       have r₂ := eq80 X0 (σ X0)
       grind)
    | exact resolve eq157 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X0
       have r₂ := eq80 X0 (σ X0)
       grind)
    | exact resolve eq180 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq180
  have eq208 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq209 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq189
  have eq221 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq208
    | (have j0 := eq208 X0 X1
       grind)
    | exact resolve eq208 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq222 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq209
    | (have j0 := eq209 X0 X1
       grind)
    | exact resolve eq209 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq228 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       have j1 := eq222 X0 X1
       grind)
    | (have r₁ := eq224 X0 X1
       have r₂ := eq222 X0 X1
       grind)
    | exact resolve eq224 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq224
  have eq232 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq228
    | exact resolve eq228 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq228 x y
       grind)
    | exact superpose eq228 eq14
    | exact resolve eq14 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq610 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq232 X0 (τ X1)
       grind)
    | exact superpose eq232 eq15
    | exact resolve eq15 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq232
  have eq642 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq610 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq610
    | exact resolve eq610 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq656 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq642
    | exact resolve eq642 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq813 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq248
       have i₂ := eq656 x y
       grind)
    | exact superpose eq656 eq248
    | exact resolve eq248 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq656
  have eq814 : False := by grind
  exact eq814

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq59 X1 X0
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq61 X1 X0
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq61 X1 X1
       have r₂ := eq59 X1 X1
       grind)
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq61
  have eq334 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq347 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq334 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq334 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq334 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq334 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq334 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq533 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq347 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq347 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq347 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq347 X1 X1
       grind)
    | exact resolve eq10 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq889 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq900 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq889 X0 X1
       have j1 := eq347 X0 X1
       grind)
    | (have r₁ := eq889 X0 X1
       have r₂ := eq347 X0 X1
       grind)
    | (have r₁ := eq889 X1 X1
       have r₂ := eq347 X1 X1
       grind)
    | exact resolve eq889 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq889
  have eq1166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq900 (σ X0) (σ X1)
       grind)
    | exact superpose eq900 eq13
    | exact resolve eq13 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1166 X0 X1
       have i₂ := eq900 X0 X1
       grind)
    | exact superpose eq900 eq1166
    | exact resolve eq1166 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq1166
  have eq2798 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1177 x y
       grind)
    | exact superpose eq1177 eq14
    | (have r₁ := eq14
       have r₂ := eq1177 x y
       grind)
    | exact resolve eq14 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq2857 : False := by grind
  exact eq2857

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq49
    | (have j0 := eq49 (σ X0) (σ X1)
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq101 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq98 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq98 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq218 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       have j1 := eq106 X0 X1
       grind)
    | (have r₁ := eq214 X0 X1
       have r₂ := eq106 X0 X1
       grind)
    | exact resolve eq214 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq214
  have eq384 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq101 X0 (τ X1)
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 X0 (τ X1)
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq101
  have eq657 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq218 x y
       grind)
    | exact superpose eq218 eq14
    | (have j1 := eq218 x y
       grind)
    | exact resolve eq14 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2043 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq384
    | exact resolve eq384 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq2130 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2043 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2043
    | (have j0 := eq2043 X0 X1
       grind)
    | exact resolve eq2043 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2876 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq657
       have i₂ := eq2130 y x
       grind)
    | exact superpose eq2130 eq657
    | (have j1 := eq2130 (σ y) (σ x)
       grind)
    | (have r₁ := eq657
       have r₂ := eq2130 y x
       grind)
    | exact resolve eq657 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq2877 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2876
  have eq3179 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2877
       grind)
    | exact superpose eq2877 eq14
    | exact resolve eq14 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3181 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2877
       grind)
    | exact superpose eq2877 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2877
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2877
       grind)
    | exact resolve eq11 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3184 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3181
  have eq3187 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3184
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq3184
    | exact resolve eq3184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3184
  have eq3192 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3187
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3187
    | exact resolve eq3187 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq12748 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2130 y x
       have i₂ := eq3192
       grind)
    | exact superpose eq3192 eq2130
    | (have j0 := eq2130 y x
       grind)
    | exact resolve eq2130 eq3192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq12823 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq12748
  have eq12855 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12823
       have r₂ := eq3179
       grind)
    | exact resolve eq12823 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq13220 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (M.op x x)
       have i₂ := eq12855
       grind)
    | exact superpose eq12855 eq8
    | exact resolve eq8 eq12855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12855
  have eq13308 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13220
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq13220
    | exact resolve eq13220 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13220
  have eq13573 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13308
       grind)
    | exact superpose eq13308 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq13308
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq13308
       grind)
    | exact resolve eq11 eq13308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13575 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq13573
  have eq13576 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq13575
  have eq13861 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq671 x y
       have i₂ := eq13576
       grind)
    | exact superpose eq13576 eq671
    | (have j0 := eq671 x y
       grind)
    | exact resolve eq671 eq13576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13576
  have eq13883 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq13861
  have eq14821 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq13883
       grind)
    | exact superpose eq13883 eq14
    | exact resolve eq14 eq13883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13883
  have eq15123 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14821
       have i₂ := eq13308
       grind)
    | exact superpose eq13308 eq14821
    | exact resolve eq14821 eq13308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13308 eq14821
  have eq15124 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq15123
  have eq15125 : x = (M.op x x) := by grind
  clear eq15124
  have eq15401 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x x
       have i₂ := eq15125
       grind)
    | exact superpose eq15125 eq10
    | exact resolve eq10 eq15125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15403 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq74 x x
       have i₂ := eq15125
       grind)
    | exact superpose eq15125 eq74
    | exact resolve eq74 eq15125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq15125
  have eq15598 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15403 (σ y)
       have i₂ := eq2877
       grind)
    | exact superpose eq2877 eq15403
    | (have j0 := eq15403 (σ y)
       grind)
    | (have r₁ := eq15403 (σ y)
       have r₂ := eq2877
       grind)
    | exact resolve eq15403 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877 eq15403
  have eq15614 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15598
  have eq15626 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15614
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq15614
    | exact resolve eq15614 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15614
  have eq15723 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2130 y x
       have i₂ := eq15626
       grind)
    | exact superpose eq15626 eq2130
    | (have j0 := eq2130 y x
       grind)
    | exact resolve eq2130 eq15626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq15726 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq15626
       grind)
    | exact superpose eq15626 eq8
    | exact resolve eq8 eq15626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626
  have eq15807 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq15723
  have eq15842 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15726
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15726
    | exact resolve eq15726 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15726
  have eq15843 : x = (M.op x y) := by
    first
    | (have r₁ := eq15807
       have r₂ := eq3179
       grind)
    | exact resolve eq15807 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179 eq15807
  have eq15853 : x = (k x y) := by
    first
    | (have j1 := eq15401 y
       grind)
    | (have r₁ := eq15842
       have r₂ := eq15401 y
       grind)
    | exact resolve eq15842 eq15401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15401 eq15842
  have eq16785 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq671 x y
       have i₂ := eq15853
       grind)
    | exact superpose eq15853 eq671
    | (have j0 := eq671 x y
       grind)
    | exact resolve eq671 eq15853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq15853
  have eq16809 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16785
  have eq17512 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16809
       grind)
    | exact superpose eq16809 eq14
    | exact resolve eq14 eq16809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq17530 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq17512
       have i₂ := eq15843
       grind)
    | exact superpose eq15843 eq17512
    | exact resolve eq17512 eq15843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15843 eq17512
  have eq17531 : False := by grind
  exact eq17531

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq10 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq49
    | (have j0 := eq49 (σ X0) (σ X1)
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq99 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq99 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq99 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       have j1 := eq107 X0 X1
       grind)
    | (have r₁ := eq214 X0 X1
       have r₂ := eq107 X0 X1
       grind)
    | exact resolve eq214 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq214
  have eq365 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq102 (τ X0) X1
       grind)
    | exact superpose eq102 eq15
    | (have j1 := eq102 (τ X0) X1
       grind)
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq102
  have eq641 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq216 x y
       grind)
    | exact superpose eq216 eq14
    | (have j1 := eq216 x y
       grind)
    | exact resolve eq14 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2031 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq365
    | exact resolve eq365 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq2114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2031 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2031
    | (have j0 := eq2031 X0 X1
       grind)
    | exact resolve eq2031 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2594 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq641
       have i₂ := eq2114 x y
       grind)
    | exact superpose eq2114 eq641
    | (have j1 := eq2114 (σ x) (σ y)
       grind)
    | (have r₁ := eq641
       have r₂ := eq2114 x y
       grind)
    | exact resolve eq641 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq2595 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2594
  have eq2620 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2595
       grind)
    | exact superpose eq2595 eq14
    | exact resolve eq14 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2622 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2595
       grind)
    | exact superpose eq2595 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2595
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2595
       grind)
    | exact resolve eq11 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2625 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2622
  have eq2626 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2625
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq2625
    | exact resolve eq2625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2625
  have eq2630 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2626
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2626
    | exact resolve eq2626 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq12021 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2114 x y
       have i₂ := eq2630
       grind)
    | exact superpose eq2630 eq2114
    | (have j0 := eq2114 x y
       grind)
    | exact resolve eq2114 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630
  have eq12097 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq12021
  have eq12129 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12097
       have r₂ := eq2620
       grind)
    | exact resolve eq12097 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097
  have eq12461 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (M.op x x)
       have i₂ := eq12129
       grind)
    | exact superpose eq12129 eq8
    | exact resolve eq8 eq12129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12129
  have eq12549 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12461
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq12461
    | exact resolve eq12461 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12461
  have eq12901 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq12549
       grind)
    | exact superpose eq12549 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq12549
       grind)
    | exact resolve eq11 eq12549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12903 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq12901
  have eq12904 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq12903
  have eq13289 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq655 x y
       have i₂ := eq12904
       grind)
    | exact superpose eq12904 eq655
    | (have j0 := eq655 x y
       grind)
    | exact resolve eq655 eq12904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12904
  have eq13311 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq13289
  have eq13656 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq13311
       grind)
    | exact superpose eq13311 eq14
    | exact resolve eq14 eq13311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13311
  have eq13922 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13656
       have i₂ := eq12549
       grind)
    | exact superpose eq12549 eq13656
    | exact resolve eq13656 eq12549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12549 eq13656
  have eq13923 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq13922
  have eq13924 : y = (M.op x x) := by grind
  clear eq13923
  have eq14286 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x x
       have i₂ := eq13924
       grind)
    | exact superpose eq13924 eq10
    | exact resolve eq10 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14290 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ y) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq75 x x
       have i₂ := eq13924
       grind)
    | exact superpose eq13924 eq75
    | exact resolve eq75 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq13924
  have eq15079 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14290 (σ y)
       have i₂ := eq2595
       grind)
    | exact superpose eq2595 eq14290
    | (have j0 := eq14290 (σ y)
       grind)
    | (have r₁ := eq14290 (σ y)
       have r₂ := eq2595
       grind)
    | exact resolve eq14290 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595 eq14290
  have eq15096 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15079
  have eq15103 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15096
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq15096
    | exact resolve eq15096 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15096
  have eq15395 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2114 x y
       have i₂ := eq15103
       grind)
    | exact superpose eq15103 eq2114
    | (have j0 := eq2114 x y
       grind)
    | exact resolve eq2114 eq15103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq15398 : (k x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq15103
       grind)
    | exact superpose eq15103 eq8
    | exact resolve eq8 eq15103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq15479 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq15395
  have eq15514 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15398
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15398
    | exact resolve eq15398 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15398
  have eq15515 : y = (M.op x y) := by
    first
    | (have r₁ := eq15479
       have r₂ := eq2620
       grind)
    | exact resolve eq15479 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620 eq15479
  have eq15524 : y = (k x y) := by
    first
    | (have j1 := eq14286 y
       grind)
    | (have r₁ := eq15514
       have r₂ := eq14286 y
       grind)
    | exact resolve eq15514 eq14286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14286 eq15514
  have eq15759 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq655 x y
       have i₂ := eq15524
       grind)
    | exact superpose eq15524 eq655
    | (have j0 := eq655 x y
       grind)
    | exact resolve eq655 eq15524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq15524
  have eq15783 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15759
  have eq16729 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15783
       grind)
    | exact superpose eq15783 eq14
    | exact resolve eq14 eq15783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15783
  have eq16743 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq16729
       have i₂ := eq15515
       grind)
    | exact superpose eq15515 eq16729
    | exact resolve eq16729 eq15515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15515 eq16729
  have eq16744 : False := by grind
  exact eq16744

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq62 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq62 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq194 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq194 X0 X1
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq194 X0 X0
       have r₂ := eq64 X0 X0
       grind)
    | exact resolve eq194 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq194
  have eq224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq199 (σ X1) (σ X0)
       grind)
    | exact superpose eq199 eq13
    | exact resolve eq13 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq199 X1 X0
       grind)
    | exact superpose eq199 eq224
    | exact resolve eq224 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq224
  have eq1574 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq231 x y
       grind)
    | exact superpose eq231 eq14
    | (have r₁ := eq14
       have r₂ := eq231 x y
       grind)
    | exact resolve eq14 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq1600 : False := by grind
  exact eq1600

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pxy_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq10 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq50 (σ X1) (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq50 X1 (τ X0)
       grind)
    | exact superpose eq50 eq16
    | (have j1 := eq50 X1 (τ X0)
       grind)
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq50
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
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
  have eq393 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq71
    | exact resolve eq71 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq433 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq603 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2464 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq603
       have i₂ := eq433 x y
       grind)
    | exact superpose eq433 eq603
    | (have j1 := eq433 (σ x) (σ y)
       grind)
    | (have r₁ := eq603
       have r₂ := eq433 x y
       grind)
    | exact resolve eq603 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq2465 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2464
  have eq2469 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2465
       grind)
    | exact superpose eq2465 eq14
    | exact resolve eq14 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2470 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2465
       grind)
    | exact superpose eq2465 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2465
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2465
       grind)
    | exact resolve eq11 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2472 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2470
  have eq2474 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2472
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq2472
    | exact resolve eq2472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2472
  have eq2477 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2474
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2474
    | exact resolve eq2474 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq40279 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq2477
       grind)
    | exact superpose eq2477 eq77
    | (have j0 := eq77 y (σ x)
       grind)
    | (have r₁ := eq77 y (σ x)
       have r₂ := eq2477
       grind)
    | exact resolve eq77 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2477
  have eq40285 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq40279
  have eq40291 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40285
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq40285
    | exact resolve eq40285 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40285
  have eq69868 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2465
       have i₂ := eq40291
       grind)
    | exact superpose eq40291 eq2465
    | exact resolve eq2465 eq40291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465 eq40291
  have eq69877 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq69868
  have eq70998 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq433 x y
       have i₂ := eq69877
       grind)
    | exact superpose eq69877 eq433
    | (have j0 := eq433 x y
       grind)
    | exact resolve eq433 eq69877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq69877
  have eq71080 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq70998
  have eq71105 : y = (M.op x y) := by
    first
    | (have r₁ := eq71080
       have r₂ := eq2469
       grind)
    | exact resolve eq71080 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469 eq71080
  have eq72167 : y ≠ y ∨ (M.op y y) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq71105
       grind)
    | exact superpose eq71105 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq71105
       grind)
    | exact resolve eq11 eq71105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72168 : y = (k y x) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq72167
  have eq73584 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq612 x y
       have i₂ := eq72168
       grind)
    | exact superpose eq72168 eq612
    | (have j0 := eq612 x y
       grind)
    | exact resolve eq612 eq72168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72168
  have eq73653 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq73584
  have eq75098 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73653
       grind)
    | exact superpose eq73653 eq14
    | exact resolve eq14 eq73653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73653
  have eq75108 : (σ y) ≠ (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq75098
       have i₂ := eq71105
       grind)
    | exact superpose eq71105 eq75098
    | exact resolve eq75098 eq71105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75098
  have eq75109 : (M.op y y) = (M.op y x) := by grind
  clear eq75108
  have eq76208 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq75109
       grind)
    | exact superpose eq75109 eq10
    | (have j0 := eq10 y X0
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq75109
       grind)
    | exact resolve eq10 eq75109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75109
  have eq76569 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq76208 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76208
  have eq76571 : y = (k y x) := by
    first
    | (have i₁ := eq76569
       have i₂ := eq71105
       grind)
    | exact superpose eq71105 eq76569
    | exact resolve eq76569 eq71105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76569
  have eq76899 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq612 x y
       have i₂ := eq76571
       grind)
    | exact superpose eq76571 eq612
    | (have j0 := eq612 x y
       grind)
    | exact resolve eq612 eq76571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq76571
  have eq76970 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq76899
  have eq78763 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq76970
       grind)
    | exact superpose eq76970 eq14
    | exact resolve eq14 eq76970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76970
  have eq78773 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq78763
       have i₂ := eq71105
       grind)
    | exact superpose eq71105 eq78763
    | exact resolve eq78763 eq71105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71105 eq78763
  have eq78774 : False := by grind
  exact eq78774
