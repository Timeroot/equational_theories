import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq75 X0 X0
       have r₂ := eq10 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq75 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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

/-- `x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq54 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq54 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq161 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq166 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq161 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq161 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq161 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq161 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq161
  have eq187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq166 (σ X0) (σ X1)
       grind)
    | exact superpose eq166 eq13
    | exact resolve eq13 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq187
    | exact resolve eq187 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq187
  have eq1438 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1459 : False := by grind
  exact eq1459

/-- `x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq294 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq301 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq306 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq304
    | (have j0 := eq304 X0 X1
       grind)
    | exact resolve eq304 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq307 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq308 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X0
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
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq354 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq361 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq366 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq364
    | (have j0 := eq364 X0 X1
       grind)
    | exact resolve eq364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq367 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq368 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X0
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
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq414
  have eq2756 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq10
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq415
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq415
       grind)
    | exact resolve eq10 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2758 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2756
  have eq2759 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2758
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2758
    | exact resolve eq2758 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq19231 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2759
       grind)
    | exact superpose eq2759 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2759
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2759
       grind)
    | exact resolve eq11 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19232 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq2759
       grind)
    | exact superpose eq2759 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq2759
       grind)
    | exact resolve eq10 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq19233 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19231
  have eq19235 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19232
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq19232
    | exact resolve eq19232 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19232
  have eq19236 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19233
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq19233
    | exact resolve eq19233 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19233
  have eq19238 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19236
       have r₂ := eq19235
       grind)
    | exact resolve eq19236 eq19235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19235 eq19236
  have eq19707 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq19238
       grind)
    | exact superpose eq19238 eq8
    | exact resolve eq8 eq19238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19238
  have eq19854 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19707
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq19707
    | exact resolve eq19707 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19707
  have eq19857 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq369 x y
       grind)
    | (have r₁ := eq19854
       have r₂ := eq369 x y
       grind)
    | exact resolve eq19854 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq19854
  have eq20097 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq19857
       grind)
    | exact superpose eq19857 eq8
    | exact resolve eq8 eq19857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19857
  have eq20244 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20097
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq20097
    | exact resolve eq20097 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20097
  have eq20245 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 x y
       grind)
    | (have r₁ := eq20244
       have r₂ := eq309 x y
       grind)
    | exact resolve eq20244 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq20244
  have eq20476 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq20245
       grind)
    | exact superpose eq20245 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq20245
       grind)
    | exact resolve eq10 eq20245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20477 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq20478 : y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq20476
  have eq21001 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65 x y
       have i₂ := eq20478
       grind)
    | exact superpose eq20478 eq65
    | (have j0 := eq65 x y
       grind)
    | exact resolve eq65 eq20478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq21045 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21001
  have eq26240 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21045
       grind)
    | exact superpose eq21045 eq14
    | exact resolve eq14 eq21045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21045
  have eq26916 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26240
       have i₂ := eq20245
       grind)
    | exact superpose eq20245 eq26240
    | exact resolve eq26240 eq20245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26240
  have eq26919 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26916
  have eq26920 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26919
       have r₂ := eq20477
       grind)
    | exact resolve eq26919 eq20477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26919
  have eq27342 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26920
       grind)
    | exact superpose eq26920 eq14
    | exact resolve eq14 eq26920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27343 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq26920
       grind)
    | exact superpose eq26920 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq26920
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq26920
       grind)
    | exact resolve eq11 eq26920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27344 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq26920
       grind)
    | exact superpose eq26920 eq10
    | exact resolve eq10 eq26920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26920
  have eq27345 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27343
  have eq27348 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
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
  have eq27349 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27345
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq27345
    | exact resolve eq27345 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27345
  have eq27351 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27349
       have r₂ := eq27348
       grind)
    | exact resolve eq27349 eq27348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27348 eq27349
  have eq27723 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27342
       have i₂ := eq20245
       grind)
    | exact superpose eq20245 eq27342
    | exact resolve eq27342 eq20245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20245 eq27342
  have eq27727 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27723
       have r₂ := eq20477
       grind)
    | exact resolve eq27723 eq20477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20477 eq27723
  have eq28420 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27351
       have i₂ := eq20478
       grind)
    | exact superpose eq20478 eq27351
    | exact resolve eq27351 eq20478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20478 eq27351
  have eq28572 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28420
  have eq28630 : x = (M.op x y) := by
    first
    | (have r₁ := eq28572
       have r₂ := eq27727
       grind)
    | exact resolve eq28572 eq27727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27727 eq28572
  have eq28960 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq28630
       grind)
    | exact superpose eq28630 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq28630
       grind)
    | exact resolve eq11 eq28630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28961 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq28630
       grind)
    | exact superpose eq28630 eq10
    | exact resolve eq10 eq28630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28962 : x = y ∨ x = (k x y) := by grind
  clear eq28960
  have eq28963 : x = (k x y) := by
    first
    | (have r₁ := eq28962
       have r₂ := eq28961
       grind)
    | exact resolve eq28962 eq28961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28961 eq28962
  have eq29349 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq28963
       grind)
    | exact superpose eq28963 eq64
    | (have j0 := eq64 x y
       grind)
    | exact resolve eq64 eq28963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq29376 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29349
  have eq33519 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq29376
       grind)
    | exact superpose eq29376 eq10
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq29376
       grind)
    | exact resolve eq10 eq29376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33520 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29376
  have eq33521 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33519
  have eq33522 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33521
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq33521
    | exact resolve eq33521 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33521
  have eq33525 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33522
       have i₂ := eq28963
       grind)
    | exact superpose eq28963 eq33522
    | exact resolve eq33522 eq28963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28963 eq33522
  have eq33527 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33525
       have r₂ := eq33520
       grind)
    | exact resolve eq33525 eq33520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33520 eq33525
  have eq33805 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33527
       grind)
    | exact superpose eq33527 eq14
    | exact resolve eq14 eq33527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33527
  have eq33811 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq33805
       have i₂ := eq28630
       grind)
    | exact superpose eq28630 eq33805
    | exact resolve eq33805 eq28630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28630 eq33805
  have eq33812 : False := by grind
  exact eq33812

/-- `x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq42 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq294 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq301 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq306 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq304
    | (have j0 := eq304 X0 X1
       grind)
    | exact resolve eq304 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq307 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq308 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X0
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
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq354 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq361 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq366 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq364
    | (have j0 := eq364 X0 X1
       grind)
    | exact resolve eq364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq367 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq368 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X0
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
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq414
  have eq2218 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq415
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq415
       grind)
    | exact resolve eq10 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2220 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2218
  have eq2221 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2220
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2220
    | exact resolve eq2220 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq17891 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2221
       grind)
    | exact superpose eq2221 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2221
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2221
       grind)
    | exact resolve eq11 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17892 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq2221
       grind)
    | exact superpose eq2221 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq2221
       grind)
    | exact resolve eq10 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq17893 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17891
  have eq17896 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17892
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq17892
    | exact resolve eq17892 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17892
  have eq17897 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17896
  have eq17898 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17893
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq17893
    | exact resolve eq17893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17893
  have eq17900 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17898
       have r₂ := eq17897
       grind)
    | exact resolve eq17898 eq17897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17897 eq17898
  have eq18504 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq17900
       grind)
    | exact superpose eq17900 eq8
    | exact resolve eq8 eq17900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17900
  have eq18653 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18504
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq18504
    | exact resolve eq18504 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18504
  have eq18656 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq369 x y
       grind)
    | (have r₁ := eq18653
       have r₂ := eq369 x y
       grind)
    | exact resolve eq18653 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq18653
  have eq18848 : (k x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq18656
       grind)
    | exact superpose eq18656 eq8
    | exact resolve eq8 eq18656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18656
  have eq18999 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18848
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq18848
    | exact resolve eq18848 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18848
  have eq19000 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 x y
       grind)
    | (have r₁ := eq18999
       have r₂ := eq309 x y
       grind)
    | exact resolve eq18999 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq18999
  have eq19193 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq19000
       grind)
    | exact superpose eq19000 eq10
    | (have j0 := eq10 x y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq19000
       grind)
    | exact resolve eq10 eq19000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19194 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19195 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq19193
  have eq19550 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42 x y
       have i₂ := eq19195
       grind)
    | exact superpose eq19195 eq42
    | (have j0 := eq42 x y
       grind)
    | exact resolve eq42 eq19195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq19595 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19550
  have eq25416 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19595
       grind)
    | exact superpose eq19595 eq14
    | exact resolve eq14 eq19595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19595
  have eq26220 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25416
       have i₂ := eq19000
       grind)
    | exact superpose eq19000 eq25416
    | exact resolve eq25416 eq19000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25416
  have eq26223 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26220
  have eq26224 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26223
       have r₂ := eq19194
       grind)
    | exact resolve eq26223 eq19194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26223
  have eq26570 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26224
       grind)
    | exact superpose eq26224 eq14
    | exact resolve eq14 eq26224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26571 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq26224
       grind)
    | exact superpose eq26224 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq26224
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq26224
       grind)
    | exact resolve eq11 eq26224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26224
  have eq26573 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26571
  have eq26577 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26573
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq26573
    | exact resolve eq26573 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26573
  have eq27033 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26570
       have i₂ := eq19000
       grind)
    | exact superpose eq19000 eq26570
    | exact resolve eq26570 eq19000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19000 eq26570
  have eq27037 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27033
       have r₂ := eq19194
       grind)
    | exact resolve eq27033 eq19194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19194 eq27033
  have eq27955 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26577
       have i₂ := eq19195
       grind)
    | exact superpose eq19195 eq26577
    | exact resolve eq26577 eq19195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19195 eq26577
  have eq28076 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27955
  have eq28176 : x = (M.op x y) := by
    first
    | (have r₁ := eq28076
       have r₂ := eq27037
       grind)
    | exact resolve eq28076 eq27037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27037 eq28076
  have eq28516 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq28176
       grind)
    | exact superpose eq28176 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq28176
       grind)
    | exact resolve eq11 eq28176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28517 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq28176
       grind)
    | exact superpose eq28176 eq10
    | (have j0 := eq10 x y
       grind)
    | exact resolve eq10 eq28176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28518 : y = (k x y) ∨ x = y := by grind
  clear eq28516
  have eq29114 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq43 x y
       have i₂ := eq28518
       grind)
    | exact superpose eq28518 eq43
    | (have j0 := eq43 x y
       grind)
    | exact resolve eq43 eq28518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq29140 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq29114
  have eq31624 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq29140
       grind)
    | exact superpose eq29140 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq29140
       grind)
    | exact resolve eq10 eq29140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29140
  have eq31626 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31624
  have eq31627 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq31626
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq31626
    | exact resolve eq31626 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31626
  have eq32465 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq31627
       grind)
    | exact superpose eq31627 eq14
    | exact resolve eq14 eq31627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31627
  have eq32474 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq32465
       have i₂ := eq28176
       grind)
    | exact superpose eq28176 eq32465
    | exact resolve eq32465 eq28176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32465
  have eq32475 : (σ x) = (σ (k x y)) ∨ x = y := by grind
  clear eq32474
  have eq32864 : (k x y) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq32475
       grind)
    | exact superpose eq32475 eq8
    | exact resolve eq8 eq32475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32475
  have eq33032 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq32864
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq32864
    | exact resolve eq32864 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32864
  have eq33033 : x = (k x y) := by
    first
    | (have r₁ := eq33032
       have r₂ := eq28517
       grind)
    | exact resolve eq33032 eq28517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28517 eq33032
  have eq33426 : x = y ∨ x = y := by
    first
    | (have i₁ := eq28518
       have i₂ := eq33033
       grind)
    | exact superpose eq33033 eq28518
    | exact resolve eq28518 eq33033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28518
  have eq33457 : x = y := by grind
  clear eq33426
  have eq33854 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33457
       grind)
    | exact superpose eq33457 eq14
    | exact resolve eq14 eq33457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33855 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39
       have i₂ := eq33457
       grind)
    | exact superpose eq33457 eq39
    | exact resolve eq39 eq33457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq33887 : x = (M.op x x) := by
    first
    | (have i₁ := eq28176
       have i₂ := eq33457
       grind)
    | exact superpose eq33457 eq28176
    | exact resolve eq28176 eq33457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28176
  have eq33889 : x = (k x x) := by
    first
    | (have i₁ := eq33033
       have i₂ := eq33457
       grind)
    | exact superpose eq33457 eq33033
    | exact resolve eq33033 eq33457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33033 eq33457
  have eq33918 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33855
  have eq33919 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33918
       have i₂ := eq33889
       grind)
    | exact superpose eq33889 eq33918
    | exact resolve eq33918 eq33889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33889 eq33918
  have eq33920 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33854
       have i₂ := eq33887
       grind)
    | exact superpose eq33887 eq33854
    | exact resolve eq33854 eq33887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33854
  have eq33921 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33919
       have i₂ := eq33887
       grind)
    | exact superpose eq33887 eq33919
    | exact resolve eq33919 eq33887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33887 eq33919
  have eq33922 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33921
  have eq33923 : False := by grind
  exact eq33923

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq12 X1 X0
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq49 X0 (k X0 X0)
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq51 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq51 X0 (k X0 X0)
       have r₂ := eq10 X0 (k X0 X0)
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
  have eq1147 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1169 : False := by grind
  exact eq1169

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq38 X0 X1
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
  have eq75 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq203 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
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
  have eq206 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq209 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq210 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq211 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq212 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq203
  have eq214 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq789 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq858 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq789 (τ X0) X1
       grind)
    | exact superpose eq789 eq16
    | (have j1 := eq789 (τ X0) X1
       grind)
    | exact resolve eq16 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
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
  have eq967 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq968 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq969 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq968
  have eq970 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq967
  have eq971 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ y = (M.op x y) := by
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
  have eq972 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
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
  have eq2413 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq858 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq858
    | exact resolve eq858 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq2466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
  have eq14346 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
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
  have eq14351 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq14346
  have eq14631 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq2466 x y
       have i₂ := eq14351
       grind)
    | exact superpose eq14351 eq2466
    | (have j0 := eq2466 x y
       grind)
    | exact resolve eq2466 eq14351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14351
  have eq14688 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq14631
  have eq14716 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14688
       have r₂ := eq966
       grind)
    | exact resolve eq14688 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq14688
  have eq14950 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq14716
       grind)
    | exact superpose eq14716 eq214
    | (have j0 := eq214 x y
       grind)
    | (have r₁ := eq214 x y
       have r₂ := eq14716
       grind)
    | exact resolve eq214 eq14716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq14716
  have eq15012 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq14950
  have eq16401 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15012
       grind)
    | exact superpose eq15012 eq14
    | exact resolve eq14 eq15012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15012
  have eq16423 : y = (M.op x y) := by
    first
    | (have j1 := eq2466 x y
       grind)
    | (have r₁ := eq16401
       have r₂ := eq2466 x y
       grind)
    | exact resolve eq16401 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq16401
  have eq16651 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16423
       grind)
    | exact superpose eq16423 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq16423
       grind)
    | exact resolve eq11 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16654 : y = (k y x) ∨ x = (M.op y x) := by grind
  clear eq16651
  have eq16914 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq16654
       grind)
    | exact superpose eq16654 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq16654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16654
  have eq16952 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq16914
  have eq17794 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16952
       grind)
    | exact superpose eq16952 eq14
    | exact resolve eq14 eq16952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16952
  have eq17801 : (σ y) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq17794
       have i₂ := eq16423
       grind)
    | exact superpose eq16423 eq17794
    | exact resolve eq17794 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17794
  have eq17802 : x = (M.op y x) := by grind
  clear eq17801
  have eq18077 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq17802
       grind)
    | exact superpose eq17802 eq10
    | (have j0 := eq10 y x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq17802
       grind)
    | exact resolve eq10 eq17802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq18078 : (M.op x y) = (k y x) := by grind
  clear eq18077
  have eq18080 : y = (k y x) := by
    first
    | (have i₁ := eq18078
       have i₂ := eq16423
       grind)
    | exact superpose eq16423 eq18078
    | exact resolve eq18078 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18078
  have eq18363 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq18080
       grind)
    | exact superpose eq18080 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq18080
  have eq18399 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18363
  have eq18962 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18399
       grind)
    | exact superpose eq18399 eq14
    | exact resolve eq14 eq18399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18399
  have eq18968 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq18962
       have i₂ := eq16423
       grind)
    | exact superpose eq16423 eq18962
    | exact resolve eq18962 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423 eq18962
  have eq18969 : False := by grind
  exact eq18969

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
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
  have eq76 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq201 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
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
  have eq208 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq212 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq216 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq201
    | (have j0 := eq201 X0 X1
       grind)
    | exact resolve eq201 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq201
  have eq790 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq966 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq790 (τ X1) X0
       grind)
    | exact superpose eq790 eq15
    | (have j1 := eq790 (τ X1) X0
       grind)
    | exact resolve eq15 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
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
  have eq1136 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq1138 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1136
  have eq1140 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
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
  have eq1847 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq966
    | exact resolve eq966 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1904 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
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
  have eq13621 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
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
  have eq13622 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq13621
  have eq13623 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13622
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq13622
    | exact resolve eq13622 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13622
  have eq43004 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1132
       have i₂ := eq13623
       grind)
    | exact superpose eq13623 eq1132
    | exact resolve eq1132 eq13623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq13623
  have eq43023 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq43004
  have eq43336 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1904 y x
       have i₂ := eq43023
       grind)
    | exact superpose eq43023 eq1904
    | (have j0 := eq1904 y x
       grind)
    | exact resolve eq1904 eq43023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904 eq43023
  have eq43423 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq43336
  have eq43450 : x = (M.op x y) := by
    first
    | (have r₁ := eq43423
       have r₂ := eq1135
       grind)
    | exact resolve eq43423 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq43423
  have eq43743 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq43450
       grind)
    | exact superpose eq43450 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq43450
       grind)
    | exact resolve eq11 eq43450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43744 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq43743
  have eq44347 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq43744
       grind)
    | exact superpose eq43744 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq43744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43744
  have eq44409 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq44347
  have eq45016 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44409
       grind)
    | exact superpose eq44409 eq14
    | exact resolve eq14 eq44409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44409
  have eq45024 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq45016
       have i₂ := eq43450
       grind)
    | exact superpose eq43450 eq45016
    | exact resolve eq45016 eq43450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45016
  have eq45025 : x = (M.op y x) := by grind
  clear eq45024
  have eq45340 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq45025
       grind)
    | exact superpose eq45025 eq10
    | (have j0 := eq10 y x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq45025
       grind)
    | exact resolve eq10 eq45025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45025
  have eq45348 : (M.op x y) = (k y x) := by grind
  clear eq45340
  have eq45350 : x = (k y x) := by
    first
    | (have i₁ := eq45348
       have i₂ := eq43450
       grind)
    | exact superpose eq43450 eq45348
    | exact resolve eq45348 eq43450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45348
  have eq45657 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq45350
       grind)
    | exact superpose eq45350 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq45350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq45350
  have eq45717 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45657
  have eq46003 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq45717
       grind)
    | exact superpose eq45717 eq14
    | exact resolve eq14 eq45717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45717
  have eq46011 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq46003
       have i₂ := eq43450
       grind)
    | exact superpose eq43450 eq46003
    | exact resolve eq46003 eq43450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43450 eq46003
  have eq46012 : False := by grind
  exact eq46012
