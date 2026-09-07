import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq144 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq147 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq144 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact resolve eq144 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq172 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq147
  have eq176 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq176 (σ X1) (σ X0)
       grind)
    | exact superpose eq176 eq13
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq176 X1 X0
       grind)
    | exact superpose eq176 eq209
    | exact resolve eq209 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq209
  have eq1223 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq14
    | (have r₁ := eq14
       have r₂ := eq224 x y
       grind)
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1244 : False := by grind
  exact eq1244

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq144 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq147 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq144 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq144 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq172 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq147
  have eq176 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq209 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq176 (σ X0) (σ X1)
       grind)
    | exact superpose eq176 eq13
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq209
    | exact resolve eq209 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq209
  have eq1219 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq14
    | (have r₁ := eq14
       have r₂ := eq224 x y
       grind)
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1240 : False := by grind
  exact eq1240

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq191 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq213 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq214 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq219 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq214
    | (have j0 := eq214 X0 X1
       grind)
    | exact resolve eq214 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq647 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    grind
  clear eq220
  have eq657 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq647
    | (have j0 := eq647 X0 X1
       grind)
    | exact resolve eq647 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq658 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq677 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq658
    | exact resolve eq658 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq658 y x
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq898 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
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
  have eq941 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq898
    | exact resolve eq898 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq960 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq941
    | exact resolve eq941 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1158 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq696
       have i₂ := eq960 x y
       grind)
    | exact superpose eq960 eq696
    | exact resolve eq696 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq960
  have eq1159 : False := by grind
  exact eq1159

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq216 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq217 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq221 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq217
    | (have j0 := eq217 X0 X1
       grind)
    | exact resolve eq217 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq222 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq647 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq222
  have eq657 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq647
    | (have j0 := eq647 X0 X1
       grind)
    | exact resolve eq647 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq658 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq677 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq658
    | exact resolve eq658 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq658 x y
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq894 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq677 X0 (τ X1)
       grind)
    | exact superpose eq677 eq16
    | exact resolve eq16 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq677
  have eq938 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq894 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq894
    | exact resolve eq894 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq957 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
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
  have eq1148 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1149 : False := by grind
  exact eq1149

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq184 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq191 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq184 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq184 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq211 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq191
  have eq225 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq225 (σ X1) (σ X0)
       grind)
    | exact superpose eq225 eq13
    | exact resolve eq13 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq225 X1 X0
       grind)
    | exact superpose eq225 eq284
    | exact resolve eq284 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq284
  have eq1330 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq300 x y
       grind)
    | exact superpose eq300 eq14
    | (have r₁ := eq14
       have r₂ := eq300 x y
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1361 : False := by grind
  exact eq1361

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq16
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
  have eq45 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq47 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq47 (σ X1) (σ X0)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq47 (τ X1) X0
       grind)
    | exact superpose eq47 eq17
    | (have j1 := eq47 (τ X1) X0
       grind)
    | exact resolve eq17 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq47
  have eq253 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
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
  have eq282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
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
  have eq455 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq460 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq768 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq774 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq460 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq460
    | (have j0 := eq460 (τ X0) (τ X1)
       grind)
    | exact resolve eq460 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq785 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq786 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq787 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
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
  have eq877 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
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
  have eq1695 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq877
  have eq1998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq455
       have i₂ := eq282 y x
       grind)
    | exact superpose eq282 eq455
    | (have j1 := eq282 (σ y) (σ x)
       grind)
    | (have r₁ := eq455
       have r₂ := eq282 y x
       grind)
    | exact resolve eq455 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
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
  have eq2005 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1999
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1999
       grind)
    | exact resolve eq11 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2006 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2005
  have eq2007 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2006
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2006
    | exact resolve eq2006 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq15140 : (τ (M.op (σ x) (σ y))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1695 (σ x)
       have i₂ := eq2007
       grind)
    | exact superpose eq2007 eq1695
    | exact resolve eq1695 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq2007
  have eq15151 : x ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15140
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15140
    | exact resolve eq15140 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15140
  have eq15167 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x ≠ (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15151
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15151
    | exact resolve eq15151 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15151
  have eq15177 : x = (M.op x y) ∨ x ≠ (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15167
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15167
    | exact resolve eq15167 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15167
  have eq15178 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq15177
  have eq21949 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15178
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq15178
    | exact resolve eq15178 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999 eq15178
  have eq21958 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq21949
  have eq21965 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21958
       have r₂ := eq8 x
       grind)
    | exact resolve eq21958 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21958
  have eq22302 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq282 y x
       have i₂ := eq21965
       grind)
    | exact superpose eq21965 eq282
    | (have j0 := eq282 y x
       grind)
    | exact resolve eq282 eq21965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq21965
  have eq22379 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22302
  have eq22406 : x = (M.op x y) := by
    first
    | (have r₁ := eq22379
       have r₂ := eq2004
       grind)
    | exact resolve eq22379 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq22379
  have eq22690 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq22406
       grind)
    | exact superpose eq22406 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq22406
       grind)
    | exact resolve eq11 eq22406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22691 : x = (k x y) ∨ y = (M.op x x) := by grind
  clear eq22690
  have eq23055 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq460 x y
       have i₂ := eq22691
       grind)
    | exact superpose eq22691 eq460
    | (have j0 := eq460 x y
       grind)
    | exact resolve eq460 eq22691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq22691
  have eq23082 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq23055
  have eq23545 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23082
       grind)
    | exact superpose eq23082 eq14
    | exact resolve eq14 eq23082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23082
  have eq23549 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23545
       have i₂ := eq22406
       grind)
    | exact superpose eq22406 eq23545
    | exact resolve eq23545 eq22406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23545
  have eq23550 : y = (M.op x x) := by grind
  clear eq23549
  have eq23962 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq768 x
       have i₂ := eq23550
       grind)
    | exact superpose eq23550 eq768
    | exact resolve eq768 eq23550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq23550
  have eq23973 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23962
       have i₂ := eq22406
       grind)
    | exact superpose eq22406 eq23962
    | exact resolve eq23962 eq22406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23962
  have eq23974 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23973
  have eq25096 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23974
       grind)
    | exact superpose eq23974 eq14
    | exact resolve eq14 eq23974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23974
  have eq25100 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq25096
       have i₂ := eq22406
       grind)
    | exact superpose eq22406 eq25096
    | exact resolve eq25096 eq22406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22406 eq25096
  have eq25101 : False := by grind
  exact eq25101

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq47 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq47 (σ X1) (σ X0)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47 X1 (τ X0)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X1 (τ X0)
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq47
  have eq253 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq65
    | exact resolve eq65 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq282 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
  have eq455 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq460 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1880 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq455
       have i₂ := eq282 x y
       grind)
    | exact superpose eq282 eq455
    | (have j1 := eq282 (σ x) (σ y)
       grind)
    | (have r₁ := eq455
       have r₂ := eq282 x y
       grind)
    | exact resolve eq455 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
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
  have eq1887 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1881
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1881
       grind)
    | exact resolve eq11 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1888 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1887
  have eq1889 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1888
    | exact resolve eq1888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq14945 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq1889
  have eq14954 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14945
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq14945
    | exact resolve eq14945 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14945
  have eq62623 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1881
       have i₂ := eq14954
       grind)
    | exact superpose eq14954 eq1881
    | exact resolve eq1881 eq14954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881 eq14954
  have eq62631 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq62623
  have eq63553 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq282 x y
       have i₂ := eq62631
       grind)
    | exact superpose eq62631 eq282
    | (have j0 := eq282 x y
       grind)
    | exact resolve eq282 eq62631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq62631
  have eq63632 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq63553
  have eq63659 : y = (M.op x y) := by
    first
    | (have r₁ := eq63632
       have r₂ := eq1886
       grind)
    | exact resolve eq63632 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq63632
  have eq64581 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq63659
       grind)
    | exact superpose eq63659 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq63659
       grind)
    | exact resolve eq11 eq63659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64582 : y = (k x y) ∨ y = (M.op x x) := by grind
  clear eq64581
  have eq65545 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq460 x y
       have i₂ := eq64582
       grind)
    | exact superpose eq64582 eq460
    | (have j0 := eq460 x y
       grind)
    | exact resolve eq460 eq64582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64582
  have eq65601 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq65545
  have eq67551 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65601
       grind)
    | exact superpose eq65601 eq14
    | exact resolve eq14 eq65601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65601
  have eq67557 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq67551
       have i₂ := eq63659
       grind)
    | exact superpose eq63659 eq67551
    | exact resolve eq67551 eq63659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67551
  have eq67558 : y = (M.op x x) := by grind
  clear eq67557
  have eq68527 : (M.op x y) = (k x y) := by grind
  clear eq67558
  have eq68538 : y = (k x y) := by
    first
    | (have i₁ := eq68527
       have i₂ := eq63659
       grind)
    | exact superpose eq63659 eq68527
    | exact resolve eq68527 eq63659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68527
  have eq69556 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq460 x y
       have i₂ := eq68538
       grind)
    | exact superpose eq68538 eq460
    | (have j0 := eq460 x y
       grind)
    | exact resolve eq460 eq68538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq68538
  have eq69612 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq69556
  have eq71649 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69612
       grind)
    | exact superpose eq69612 eq14
    | exact resolve eq14 eq69612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69612
  have eq71655 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq71649
       have i₂ := eq63659
       grind)
    | exact superpose eq63659 eq71649
    | exact resolve eq71649 eq63659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63659 eq71649
  have eq71656 : False := by grind
  exact eq71656

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq184 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq191 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq184 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq184 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq211 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq191
  have eq225 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq225 (σ X0) (σ X1)
       grind)
    | exact superpose eq225 eq13
    | exact resolve eq13 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq225 X0 X1
       grind)
    | exact superpose eq225 eq284
    | exact resolve eq284 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq284
  have eq1330 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq300 x y
       grind)
    | exact superpose eq300 eq14
    | (have r₁ := eq14
       have r₂ := eq300 x y
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1361 : False := by grind
  exact eq1361
