import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
       have r₂ := eq12 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq95 (k X0 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq95 (M.op X0 X0) (k X0 X1)
       grind)
    | exact resolve eq149 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq149
  have eq267 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq91 X0 (τ X1)
       grind)
    | exact superpose eq91 eq17
    | (have j1 := eq91 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq17 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq91
  have eq595 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq267
    | exact resolve eq267 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq632 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq595
    | (have j0 := eq595 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq595 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq649 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq14
    | (have j1 := eq157 x y
       grind)
    | exact resolve eq14 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq649
       have i₂ := eq632 y x
       grind)
    | exact superpose eq632 eq649
    | (have j1 := eq632 (σ x) (σ y)
       grind)
    | (have r₁ := eq649
       have r₂ := eq632 y x
       grind)
    | (have r₁ := eq649
       have r₂ := eq632 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq649
       have r₂ := eq632 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq649 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq649
  have eq1012 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1011
  have eq1125 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq8
    | exact resolve eq8 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1161 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1125
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1125
    | exact resolve eq1125 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1162 : x = y := by grind
  clear eq1161
  have eq1234 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq14
    | exact resolve eq14 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1235 : False := by grind
  exact eq1235

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq149 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq149 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq95 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq95 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq149 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq149
  have eq267 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq91 X1 (τ X0)
       grind)
    | exact superpose eq91 eq17
    | (have j1 := eq91 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq17 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq91
  have eq597 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq267 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq267
    | exact resolve eq267 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq634 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq597
    | (have j0 := eq597 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq597 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq651 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq14
    | (have j1 := eq157 x y
       grind)
    | exact resolve eq14 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1013 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq651
       have i₂ := eq634 x y
       grind)
    | exact superpose eq634 eq651
    | (have j1 := eq634 (σ x) (σ y)
       grind)
    | (have r₁ := eq651
       have r₂ := eq634 x y
       grind)
    | (have r₁ := eq651
       have r₂ := eq634 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq651
       have r₂ := eq634 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq651 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq651
  have eq1014 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1013
  have eq1126 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq8
    | exact resolve eq8 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1162 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1126
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1126
    | exact resolve eq1126 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1163 : x = y := by grind
  clear eq1162
  have eq1235 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq14
    | exact resolve eq14 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1236 : False := by grind
  exact eq1236

/-- `x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq19 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq20 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq19
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq28
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X2 X0) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq27
    | exact resolve eq27 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq106
    | (have j0 := eq106 X0 X1
       grind)
    | exact resolve eq106 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq464 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq465 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq464 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq547 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq548 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq847 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq465 X1 (τ X0)
       grind)
    | exact superpose eq465 eq17
    | (have j1 := eq465 X1 (τ X0)
       grind)
    | exact resolve eq17 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq465 (σ X1) (σ X0)
       grind)
    | exact superpose eq465 eq13
    | (have j1 := eq465 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq881 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq848 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq848
    | (have j0 := eq848 X0 X1
       grind)
    | exact resolve eq848 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1005 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq548 X0 (τ X1)
       grind)
    | exact superpose eq548 eq17
    | (have j1 := eq548 X0 (τ X1)
       grind)
    | exact resolve eq17 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2304 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X2 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq11
    | (have j0 := eq11 X1 X2
       have j1 := eq115 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq115 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq115 X0 X1
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2549 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ X2) = X1 ∨ (M.op X1 (σ X2)) = (k (σ X2) X1) ∨ (k X0 (σ X2)) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X2 X1
       have i₂ := eq40 X0 X2
       grind)
    | (have i₁ := eq65 (τ X0) X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq65
    | (have j0 := eq65 X2 X1
       have j1 := eq40 X0 X2
       grind)
    | exact resolve eq65 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq65
  have eq2615 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (σ X2) = X1 ∨ (M.op X1 (σ X2)) = (k (σ X2) X1) ∨ (k X0 (σ X2)) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2549 X0 X1 X2
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq2549
    | (have j0 := eq2549 X0 X1 X2
       grind)
    | (have r₁ := eq2549 X0 X0 X2
       have r₂ := eq29 X0
       grind)
    | exact resolve eq2549 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2549
  have eq33177 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq847 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq847
    | exact resolve eq847 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq33201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33177 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq33177
    | (have j0 := eq33177 X0 X1
       grind)
    | exact resolve eq33177 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33177
  have eq38741 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1005 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq1005
    | exact resolve eq1005 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq38765 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38741 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq38741
    | (have j0 := eq38741 X0 X1
       grind)
    | exact resolve eq38741 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38741
  have eq62825 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq67273 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62825 (τ X0) (τ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq62825
    | (have j0 := eq62825 (τ X0) (τ X1)
       grind)
    | exact resolve eq62825 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq67279 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67273 X0 X1
       have i₂ := eq17 X0 (τ X1)
       grind)
    | exact superpose eq17 eq67273
    | (have j0 := eq67273 X0 X1
       grind)
    | exact resolve eq67273 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq67273
  have eq67285 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67279 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq67279
    | (have j0 := eq67279 X0 X1
       grind)
    | exact resolve eq67279 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67279
  have eq67290 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67285 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq67285
    | (have j0 := eq67285 X0 X1
       grind)
    | (have r₁ := eq67285 X1 X1
       have r₂ := eq9 (k X1 X1)
       grind)
    | exact resolve eq67285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67285
  have eq67293 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67290 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67290
    | (have j0 := eq67290 X0 X1
       grind)
    | exact resolve eq67290 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67290
  have eq67296 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67293 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq67293
    | (have j0 := eq67293 X0 X1
       grind)
    | exact resolve eq67293 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67293
  have eq67297 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67296 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq67296
    | (have j0 := eq67296 X0 X1
       grind)
    | exact resolve eq67296 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67296
  have eq67298 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67297 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq67297
    | (have j0 := eq67297 X0 X1
       grind)
    | exact resolve eq67297 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67297
  have eq67299 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67298 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67298
    | (have j0 := eq67298 X0 X1
       grind)
    | exact resolve eq67298 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67298
  have eq67326 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67299 X0 X1
       have i₂ := eq548 X0 X1
       grind)
    | exact superpose eq548 eq67299
    | (have j0 := eq67299 X0 X1
       have j1 := eq548 X0 X1
       grind)
    | (have r₁ := eq67299 X0 X1
       have r₂ := eq548 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq67299 X0 X1
       have r₂ := eq548 (k X1 X0) (k X0 X1)
       grind)
    | exact resolve eq67299 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq67299
  have eq67358 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67326 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67326
  have eq67365 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67358 X0 X1
       have j1 := eq1018 X0 X1
       grind)
    | (have r₁ := eq67358 X1 X0
       have r₂ := eq1018 X0 X1
       grind)
    | (have r₁ := eq67358 X0 X1
       have r₂ := eq1018 (M.op X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq67358 X0 X1
       have r₂ := eq1018 (k X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq67358 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq67358
  have eq71183 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2304 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq71186 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71183 x y
       grind)
    | exact superpose eq71183 eq14
    | (have j1 := eq71183 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq71183 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq71183 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq71183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71183
  have eq71187 : (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq38765 y x
       grind)
    | (have r₁ := eq71186
       have r₂ := eq38765 y x
       grind)
    | (have r₁ := eq71186
       have r₂ := eq38765 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq71186
       have r₂ := eq38765 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq71186 eq38765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38765 eq71186
  have eq71232 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67365 y x
       have i₂ := eq71187
       grind)
    | exact superpose eq71187 eq67365
    | (have j0 := eq67365 x y
       grind)
    | (have r₁ := eq67365 y x
       have r₂ := eq71187
       grind)
    | exact resolve eq67365 eq71187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67365 eq71187
  have eq71233 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq71232
  have eq71234 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq71233
  have eq71326 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62825 x y
       have i₂ := eq71234
       grind)
    | exact superpose eq71234 eq62825
    | (have j0 := eq62825 x y
       grind)
    | exact resolve eq62825 eq71234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62825 eq71234
  have eq71345 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq71326
  have eq71392 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq71345
       have r₂ := eq14
       grind)
    | exact resolve eq71345 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71345
  have eq74441 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2615 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq86652 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op (τ X0) X1)
       have i₂ := eq74441 X1 X0
       grind)
    | exact superpose eq74441 eq8
    | (have j1 := eq74441 X1 X0
       grind)
    | exact resolve eq8 eq74441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74441
  have eq86653 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86652 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq86652
    | (have j0 := eq86652 X0 X1
       grind)
    | exact resolve eq86652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq86652
  have eq86656 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86653 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq86653
    | (have j0 := eq86653 (σ X0) X1
       grind)
    | exact resolve eq86653 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86653
  have eq86661 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86656 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq86656
    | (have j0 := eq86656 X0 X1
       grind)
    | exact resolve eq86656 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86656
  have eq86668 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq86661 x y
       grind)
    | exact superpose eq86661 eq14
    | (have j1 := eq86661 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq86661 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq86661 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq86661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86661
  have eq86669 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq33201 x y
       grind)
    | (have r₁ := eq86668
       have r₂ := eq33201 x y
       grind)
    | (have r₁ := eq86668
       have r₂ := eq33201 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq86668
       have r₂ := eq33201 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq86668 eq33201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33201 eq86668
  have eq86676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq71392
       have i₂ := eq86669
       grind)
    | exact superpose eq86669 eq71392
    | exact resolve eq71392 eq86669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71392 eq86669
  have eq86690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq86676
  have eq86691 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq86690
  have eq86699 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq86691
       grind)
    | exact superpose eq86691 eq8
    | exact resolve eq8 eq86691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86691
  have eq87022 : x = y ∨ x = y := by
    first
    | (have i₁ := eq86699
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq86699
    | exact resolve eq86699 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86699
  have eq87023 : x = y := by grind
  clear eq87022
  have eq87025 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq87023
       grind)
    | exact superpose eq87023 eq14
    | exact resolve eq14 eq87023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87023
  have eq87026 : False := by grind
  exact eq87026

/-- `x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq260 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq83
    | exact resolve eq83 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq14
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq14 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq278 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq260 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq260
    | (have j0 := eq260 X0 X1
       grind)
    | exact resolve eq260 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq260
  have eq311 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq278
    | exact resolve eq278 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq478 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq266
       have i₂ := eq311 x y
       grind)
    | exact superpose eq311 eq266
    | (have j1 := eq311 (σ x) (σ y)
       grind)
    | (have r₁ := eq266
       have r₂ := eq311 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq266
       have r₂ := eq311 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq266 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq311
  have eq481 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq478
  have eq513 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq481
       grind)
    | exact superpose eq481 eq8
    | exact resolve eq8 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq548 : x = y ∨ x = y := by
    first
    | (have i₁ := eq513
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq513
    | exact resolve eq513 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq549 : x = y := by grind
  clear eq548
  have eq621 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq549
       grind)
    | exact superpose eq549 eq14
    | exact resolve eq14 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq622 : False := by grind
  exact eq622

/-- `x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq75 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq259 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq14
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq14 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq277 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq259
    | (have j0 := eq259 X0 X1
       grind)
    | exact resolve eq259 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq259
  have eq310 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq277
    | exact resolve eq277 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq477 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq265
       have i₂ := eq310 x y
       grind)
    | exact superpose eq310 eq265
    | (have j1 := eq310 (σ x) (σ y)
       grind)
    | (have r₁ := eq265
       have r₂ := eq310 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq265
       have r₂ := eq310 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq265 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq310
  have eq480 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq477
  have eq512 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq480
       grind)
    | exact superpose eq480 eq8
    | exact resolve eq8 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq547 : x = y ∨ x = y := by
    first
    | (have i₁ := eq512
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq512
    | exact resolve eq512 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq548 : x = y := by grind
  clear eq547
  have eq632 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq14
    | exact resolve eq14 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq633 : False := by grind
  exact eq633

/-- `x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
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
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq152 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       have j1 := eq98 X0 X1
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq98 (k X0 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq98 (M.op X1 X1) (k X0 X1)
       grind)
    | exact resolve eq152 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq152
  have eq268 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq92 X0 (τ X1)
       grind)
    | exact superpose eq92 eq17
    | (have j1 := eq92 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq17 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq92
  have eq594 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq268
    | exact resolve eq268 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq631 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq594
    | (have j0 := eq594 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq594 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq648 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
       have i₂ := eq631 y x
       grind)
    | exact superpose eq631 eq648
    | (have j1 := eq631 (σ x) (σ y)
       grind)
    | (have r₁ := eq648
       have r₂ := eq631 y x
       grind)
    | (have r₁ := eq648
       have r₂ := eq631 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq648
       have r₂ := eq631 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq648 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq648
  have eq1009 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1008
  have eq1122 : y = (τ (σ x)) ∨ x = y := by
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
  have eq1158 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1122
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1122
    | exact resolve eq1122 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1159 : x = y := by grind
  clear eq1158
  have eq1232 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1159
       grind)
    | exact superpose eq1159 eq14
    | exact resolve eq14 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1233 : False := by grind
  exact eq1233

/-- `x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq66 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq68 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq282 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq310 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq66
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq66
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq657
  have eq3111 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3112 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq658
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq658
       grind)
    | exact resolve eq11 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq3113 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3112
  have eq3114 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3113
  have eq3116 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3114
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3114
    | exact resolve eq3114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq5507 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq310 y x
       have i₂ := eq3116
       grind)
    | exact superpose eq3116 eq310
    | (have j0 := eq310 y x
       grind)
    | exact resolve eq310 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq5509 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq3116
       grind)
    | exact superpose eq3116 eq8
    | exact resolve eq8 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq5554 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5507
  have eq5582 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5509
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq5509
    | exact resolve eq5509 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5583 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5554
       have r₂ := eq3111
       grind)
    | exact resolve eq5554 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111 eq5554
  have eq5586 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq5582
       have r₂ := eq11 x y
       grind)
    | exact resolve eq5582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5582
  have eq5919 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq5586
       grind)
    | exact superpose eq5586 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq5586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq5586
  have eq5922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5919
  have eq5923 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5922
  have eq6116 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq5923
       grind)
    | exact superpose eq5923 eq14
    | exact resolve eq14 eq5923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5923
  have eq6317 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6116
       have i₂ := eq5583
       grind)
    | exact superpose eq5583 eq6116
    | exact resolve eq6116 eq5583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583 eq6116
  have eq6318 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6317
  have eq6319 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6318
  have eq6481 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq6319
       grind)
    | exact superpose eq6319 eq8
    | exact resolve eq8 eq6319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6319
  have eq6560 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6481
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq6481
    | exact resolve eq6481 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6481
  have eq6561 : x = y := by grind
  clear eq6560
  have eq6728 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6561
       grind)
    | exact superpose eq6561 eq14
    | exact resolve eq14 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561
  have eq6729 : False := by grind
  exact eq6729

/-- `x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq66 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq282 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq31
    | exact resolve eq31 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq658 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq66
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq66
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq658
  have eq3110 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq14
    | exact resolve eq14 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3111 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq659
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq659
       grind)
    | exact resolve eq11 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq3112 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3111
  have eq3113 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3112
  have eq3115 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3113
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3113
    | exact resolve eq3113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq5530 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq310 x y
       have i₂ := eq3115
       grind)
    | exact superpose eq3115 eq310
    | (have j0 := eq310 x y
       grind)
    | exact resolve eq310 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq5532 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq3115
       grind)
    | exact superpose eq3115 eq8
    | exact resolve eq8 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq5577 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5530
  have eq5605 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5532
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq5532
    | exact resolve eq5532 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5532
  have eq5606 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5577
       have r₂ := eq3110
       grind)
    | exact resolve eq5577 eq3110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110 eq5577
  have eq5609 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq5605
       have r₂ := eq11 x y
       grind)
    | exact resolve eq5605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605
  have eq5942 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq5609
       grind)
    | exact superpose eq5609 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq5609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq5609
  have eq5945 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5942
  have eq5946 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5945
  have eq6139 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq5946
       grind)
    | exact superpose eq5946 eq14
    | exact resolve eq14 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946
  have eq6340 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6139
       have i₂ := eq5606
       grind)
    | exact superpose eq5606 eq6139
    | exact resolve eq6139 eq5606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5606 eq6139
  have eq6341 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6340
  have eq6342 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6341
  have eq6502 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq6342
       grind)
    | exact superpose eq6342 eq8
    | exact resolve eq8 eq6342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6342
  have eq6581 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6502
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq6502
    | exact resolve eq6502 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502
  have eq6582 : x = y := by grind
  clear eq6581
  have eq6747 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6582
       grind)
    | exact superpose eq6582 eq14
    | exact resolve eq14 eq6582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6748 : False := by grind
  exact eq6748
