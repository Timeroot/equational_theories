import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq185 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq192 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq185 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq185 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | exact resolve eq185 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq185
  have eq212 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq192
  have eq226 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq226 (σ X0) (σ X1)
       grind)
    | exact superpose eq226 eq13
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq226 X0 X1
       grind)
    | exact superpose eq226 eq289
    | exact resolve eq289 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq289
  have eq1032 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq14
    | (have r₁ := eq14
       have r₂ := eq298 x y
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1059 : False := by grind
  exact eq1059

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq192 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq185 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq185 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | exact resolve eq185 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq185
  have eq212 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq192
  have eq226 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq226 (σ X1) (σ X0)
       grind)
    | exact superpose eq226 eq13
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq226 X1 X0
       grind)
    | exact superpose eq226 eq289
    | exact resolve eq289 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq289
  have eq1032 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq14
    | (have r₁ := eq14
       have r₂ := eq298 x y
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1059 : False := by grind
  exact eq1059

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq45 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq45 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq45 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq11 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq215 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq216 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq221 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq216
    | (have j0 := eq216 X0 X1
       grind)
    | exact resolve eq216 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq222 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq648 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq222
  have eq658 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq648
    | (have j0 := eq648 X0 X1
       grind)
    | exact resolve eq648 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq659 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq677 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq659
    | exact resolve eq659 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq659 x y
       grind)
    | exact superpose eq659 eq14
    | exact resolve eq14 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq895 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq677 X0 (τ X1)
       grind)
    | exact superpose eq677 eq17
    | exact resolve eq17 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq677
  have eq938 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq895 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq895
    | exact resolve eq895 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq957 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq938 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq938
    | exact resolve eq938 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1156 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq696
       have i₂ := eq957 x y
       grind)
    | exact superpose eq957 eq696
    | exact resolve eq696 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq957
  have eq1157 : False := by grind
  exact eq1157

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq191 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq45 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq45 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq45 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq11 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq219 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq219
    | (have j0 := eq219 X0 X1
       grind)
    | exact resolve eq219 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq650 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    grind
  clear eq224
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq661 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq680 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq661 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq661
    | exact resolve eq661 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq661 y x
       grind)
    | exact superpose eq661 eq14
    | exact resolve eq14 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq900 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq680 X0 (τ X1)
       grind)
    | exact superpose eq680 eq16
    | exact resolve eq16 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq680
  have eq944 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq900
    | exact resolve eq900 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq963 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq944
    | exact resolve eq944 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1155 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq699
       have i₂ := eq963 x y
       grind)
    | exact superpose eq963 eq699
    | exact resolve eq699 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq963
  have eq1156 : False := by grind
  exact eq1156

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq53 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq145 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq148 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq145 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact resolve eq145 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq173 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq148
  have eq177 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq177 (σ X0) (σ X1)
       grind)
    | exact superpose eq177 eq13
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq214
    | exact resolve eq214 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq214
  have eq745 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq223 x y
       grind)
    | exact superpose eq223 eq14
    | (have r₁ := eq14
       have r₂ := eq223 x y
       grind)
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq765 : False := by grind
  exact eq765

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq63 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq48 X0 (τ X1)
       grind)
    | exact superpose eq48 eq17
    | (have j1 := eq48 X0 (τ X1)
       grind)
    | exact resolve eq17 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq48 (σ X0) (σ X1)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq252 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq63
    | exact resolve eq63 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | exact resolve eq252 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq456 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq461 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1974 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq456
       have i₂ := eq281 y x
       grind)
    | exact superpose eq281 eq456
    | (have j1 := eq281 (σ y) (σ x)
       grind)
    | (have r₁ := eq456
       have r₂ := eq281 y x
       grind)
    | exact resolve eq456 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1975 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1974
  have eq1979 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1975
       grind)
    | exact superpose eq1975 eq14
    | exact resolve eq14 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1980 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1975
       grind)
    | exact superpose eq1975 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1975
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1975
       grind)
    | exact resolve eq11 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1981 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1980
  have eq1982 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1981
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1981
    | exact resolve eq1981 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq14634 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq1982
  have eq14643 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14634
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq14634
    | exact resolve eq14634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14634
  have eq69656 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1975
       have i₂ := eq14643
       grind)
    | exact superpose eq14643 eq1975
    | exact resolve eq1975 eq14643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975 eq14643
  have eq69664 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq69656
  have eq70572 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281 y x
       have i₂ := eq69664
       grind)
    | exact superpose eq69664 eq281
    | (have j0 := eq281 y x
       grind)
    | exact resolve eq281 eq69664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq69664
  have eq70651 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq70572
  have eq70678 : x = (M.op x y) := by
    first
    | (have r₁ := eq70651
       have r₂ := eq1979
       grind)
    | exact resolve eq70651 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq70651
  have eq71636 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq70678
       grind)
    | exact resolve eq11 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71637 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq71636
  have eq72567 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq461 x y
       have i₂ := eq71637
       grind)
    | exact superpose eq71637 eq461
    | (have j0 := eq461 x y
       grind)
    | exact resolve eq461 eq71637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71637
  have eq72623 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq72567
  have eq74516 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq72623
       grind)
    | exact superpose eq72623 eq14
    | exact resolve eq14 eq72623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72623
  have eq74522 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74516
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq74516
    | exact resolve eq74516 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74516
  have eq74523 : x = (M.op y y) := by grind
  clear eq74522
  have eq75474 : (M.op x y) = (k x y) := by grind
  clear eq74523
  have eq75485 : x = (k x y) := by
    first
    | (have i₁ := eq75474
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq75474
    | exact resolve eq75474 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75474
  have eq76492 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq461 x y
       have i₂ := eq75485
       grind)
    | exact superpose eq75485 eq461
    | (have j0 := eq461 x y
       grind)
    | exact resolve eq461 eq75485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq75485
  have eq76548 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq76492
  have eq78539 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq76548
       grind)
    | exact superpose eq76548 eq14
    | exact resolve eq14 eq76548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76548
  have eq78545 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq78539
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq78539
    | exact resolve eq78539 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70678 eq78539
  have eq78546 : False := by grind
  exact eq78546

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq48 (σ X0) (σ X1)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq48 (τ X0) X1
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 (τ X0) X1
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq48
  have eq252 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq67
    | exact resolve eq67 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq281 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | exact resolve eq252 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq456 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq461 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq772 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq461 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq461
    | (have j0 := eq461 (τ X0) (τ X1)
       grind)
    | exact resolve eq461 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq782 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq784 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq785 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq784 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq784
    | (have j0 := eq784 X0 X1
       grind)
    | exact resolve eq784 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq786 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq875 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq786 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq786
    | (have j0 := eq786 (τ X0) (τ X1)
       grind)
    | exact resolve eq786 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq786
  have eq1847 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq875
  have eq1889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq456
       have i₂ := eq281 x y
       grind)
    | exact superpose eq281 eq456
    | (have j1 := eq281 (σ x) (σ y)
       grind)
    | (have r₁ := eq456
       have r₂ := eq281 x y
       grind)
    | exact resolve eq456 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1890 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1889
  have eq1894 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq14
    | exact resolve eq14 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1890
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1890
       grind)
    | exact resolve eq11 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1895
  have eq1897 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1896
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1896
    | exact resolve eq1896 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq15377 : (τ (σ y)) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1847 (σ y)
       have i₂ := eq1897
       grind)
    | exact superpose eq1897 eq1847
    | exact resolve eq1847 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847 eq1897
  have eq15388 : y ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15377
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15377
    | exact resolve eq15377 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15377
  have eq15404 : y = (M.op (τ (σ x)) y) ∨ y ≠ (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15388
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15388
    | exact resolve eq15388 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15388
  have eq15414 : y = (M.op x y) ∨ y ≠ (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15404
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15404
    | exact resolve eq15404 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15404
  have eq15415 : y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq15414
  have eq22271 : y ≠ (τ (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15415
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq15415
    | exact resolve eq15415 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq15415
  have eq22279 : y ≠ (τ (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq22271
  have eq22283 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22279
       have r₂ := eq8 y
       grind)
    | exact resolve eq22279 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22279
  have eq22571 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq22283
       grind)
    | exact superpose eq22283 eq281
    | (have j0 := eq281 x y
       grind)
    | exact resolve eq281 eq22283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq22283
  have eq22648 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq22571
  have eq22675 : y = (M.op x y) := by
    first
    | (have r₁ := eq22648
       have r₂ := eq1894
       grind)
    | exact resolve eq22648 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq22648
  have eq23016 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq22675
       grind)
    | exact superpose eq22675 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq22675
       grind)
    | exact resolve eq11 eq22675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23017 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq23016
  have eq23312 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq461 x y
       have i₂ := eq23017
       grind)
    | exact superpose eq23017 eq461
    | (have j0 := eq461 x y
       grind)
    | exact resolve eq461 eq23017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq23017
  have eq23339 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq23312
  have eq23959 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23339
       grind)
    | exact superpose eq23339 eq14
    | exact resolve eq14 eq23339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23339
  have eq23963 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23959
       have i₂ := eq22675
       grind)
    | exact superpose eq22675 eq23959
    | exact resolve eq23959 eq22675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23959
  have eq23964 : x = (M.op y y) := by grind
  clear eq23963
  have eq24272 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq773 y
       have i₂ := eq23964
       grind)
    | exact superpose eq23964 eq773
    | exact resolve eq773 eq23964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq23964
  have eq24283 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24272
       have i₂ := eq22675
       grind)
    | exact superpose eq22675 eq24272
    | exact resolve eq24272 eq22675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24272
  have eq24284 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24283
  have eq25509 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq24284
       grind)
    | exact superpose eq24284 eq14
    | exact resolve eq14 eq24284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24284
  have eq25513 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25509
       have i₂ := eq22675
       grind)
    | exact superpose eq22675 eq25509
    | exact resolve eq25509 eq22675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22675 eq25509
  have eq25514 : False := by grind
  exact eq25514

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq53 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq145 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq148 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq145 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact resolve eq145 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq173 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq148
  have eq177 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq177 (σ X1) (σ X0)
       grind)
    | exact superpose eq177 eq13
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq214
    | exact resolve eq214 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq214
  have eq748 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq223 x y
       grind)
    | exact superpose eq223 eq14
    | (have r₁ := eq14
       have r₂ := eq223 x y
       grind)
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq768 : False := by grind
  exact eq768
