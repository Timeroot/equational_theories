import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = Y then X else if m(Y,X) = X then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyx_y_pyx_x_pyx_x_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    grind
  have eq40 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 (τ (M.op (σ X0) (σ X0))))
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq55 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq59 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq60 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq65 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq55
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq66 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0) X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq19
    | (have j1 := eq61 (σ X0)
       grind)
    | exact resolve eq19 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69
    | (have j0 := eq69 X0
       grind)
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X0
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq87 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63 (σ x) (σ y)
       grind)
    | exact superpose eq63 eq16
    | (have j1 := eq63 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq63 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq63 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq93 (k X0 X1) X1
       grind)
    | (have r₁ := eq95 X0 X0
       have r₂ := eq93 X0 (k X0 X0)
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq95 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq95
  have eq99 : (σ y) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq101 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq102 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq128 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq129 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by grind
  clear eq128
  have eq157 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 (σ X1) X0
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq98
    | (have j0 := eq98 (σ X0) X1
       grind)
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 (τ X0) X1
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (τ X0)
       have i₂ := eq81 (τ X0)
       grind)
    | exact superpose eq81 eq22
    | (have j1 := eq81 (τ X0)
       grind)
    | exact resolve eq22 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq187 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq183
    | (have j0 := eq183 X0
       grind)
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq191 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op X0 X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq187
    | (have j0 := eq187 X0
       grind)
    | exact resolve eq187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq103
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq103 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq103
  have eq195 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (k y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq193
  have eq196 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq191 (σ X0)
       grind)
    | exact superpose eq191 eq40
    | (have j1 := eq191 (σ X0)
       grind)
    | exact resolve eq40 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq191
  have eq198 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq196 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq196
    | (have j0 := eq196 X0
       grind)
    | exact resolve eq196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq199 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (τ (σ (k X0 (τ (σ X0))))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq19 (σ X0) X0
       grind)
    | exact superpose eq19 eq198
    | (have j0 := eq198 X0
       grind)
    | exact resolve eq198 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq200 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq199 X0
       have i₂ := eq9 (k X0 (τ (σ X0)))
       grind)
    | exact superpose eq9 eq199
    | (have j0 := eq199 X0
       grind)
    | exact resolve eq199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq201 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq200 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq200
    | (have j0 := eq200 X0
       grind)
    | exact resolve eq200 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq202 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq243 : ∀ X0 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (τ X0)
       have i₂ := eq202 (τ X0)
       grind)
    | exact superpose eq202 eq22
    | exact resolve eq22 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq243
    | exact resolve eq243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq250 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq246
    | exact resolve eq246 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq274 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq10
    | exact resolve eq10 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq274
    | exact resolve eq274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq202 X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq202
    | exact resolve eq202 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq276
  have eq316 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0) X0
       have i₂ := eq283 (σ X0)
       grind)
    | exact superpose eq283 eq19
    | exact resolve eq19 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (τ X0)
       have i₂ := eq283 (τ X0)
       grind)
    | exact superpose eq283 eq22
    | exact resolve eq22 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq318 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq317
    | exact resolve eq317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq316 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq316
    | exact resolve eq316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq318 X0
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq318
    | exact resolve eq318 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq323 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq319
    | exact resolve eq319 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq319
  have eq328 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | exact resolve eq158 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq322
  have eq337 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (σ (k X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq346 : y = (k y x) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq195
       have i₂ := eq323 y
       grind)
    | exact superpose eq323 eq195
    | exact resolve eq195 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq349 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq323 y
       grind)
    | exact superpose eq323 eq129
    | exact resolve eq129 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq400 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq411 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq400 X0
       have i₂ := eq19 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq19 eq400
    | exact resolve eq400 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq415 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq411 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq411
    | exact resolve eq411 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq417 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq415
  have eq526 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq328 X1 X0
       grind)
    | exact superpose eq328 eq10
    | (have j1 := eq328 X1 X0
       grind)
    | exact resolve eq10 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq591 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq337
    | (have j0 := eq337 X1 (σ X0)
       grind)
    | exact resolve eq337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq1374 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 (σ X1)
       have i₂ := eq19 (σ X0) X1
       grind)
    | exact superpose eq19 eq526
    | (have j0 := eq526 X1 (σ X0)
       grind)
    | exact resolve eq526 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq1389 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1374
    | (have j0 := eq1374 X0 X1
       grind)
    | exact resolve eq1374 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1393 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1389 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1389
    | (have j0 := eq1389 X0 X1
       grind)
    | exact resolve eq1389 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1396 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1393 X0 X1
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq1393
    | (have j0 := eq1393 X0 X1
       grind)
    | exact resolve eq1393 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1398 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1396 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq1396
    | (have j0 := eq1396 X0 X1
       grind)
    | exact resolve eq1396 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1400 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1402 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1400 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1400
    | (have j0 := eq1400 X0 X1
       grind)
    | exact resolve eq1400 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1404 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1402 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1402
    | (have j0 := eq1402 X0 X1
       grind)
    | exact resolve eq1402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1406 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1404 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq1404
    | (have j0 := eq1404 X0 X1
       grind)
    | exact resolve eq1404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1408 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1406 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1406
    | (have j0 := eq1406 X0 X1
       grind)
    | exact resolve eq1406 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1420 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq346
       have i₂ := eq1408 y x
       grind)
    | exact superpose eq1408 eq346
    | (have j1 := eq1408 y x
       grind)
    | exact resolve eq346 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq1422 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1424 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq1420
  have eq1427 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have j1 := eq1422 y x
       grind)
    | (have r₁ := eq1424
       have r₂ := eq1422 x y
       grind)
    | (have r₁ := eq1424
       have r₂ := eq1422 y x
       grind)
    | (have r₁ := eq1424
       have r₂ := eq1422 (σ x) (σ y)
       grind)
    | exact resolve eq1424 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq1424
  have eq1434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1427
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq1427
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1449 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq591 X0 X1
       grind)
    | exact superpose eq591 eq9
    | (have j1 := eq591 X0 X1
       grind)
    | exact resolve eq9 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq591 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq34897 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1434
       grind)
    | exact superpose eq1434 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1434
       grind)
    | exact resolve eq12 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq34901 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq34897
  have eq34924 : (σ y) = (σ (k y (τ (σ x)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq34901
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq34901
    | exact resolve eq34901 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34901
  have eq34938 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq34924
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq34924
    | exact resolve eq34924 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34924
  have eq34952 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq34938
       have i₂ := eq323 y
       grind)
    | exact superpose eq323 eq34938
    | exact resolve eq34938 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34938
  have eq34953 : x = (M.op y y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq34952
  have eq35453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq34953
       grind)
    | exact superpose eq34953 eq417
    | exact resolve eq417 eq34953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34953
  have eq35491 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq35453
       have r₂ := eq16
       grind)
    | exact resolve eq35453 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35453
  have eq35783 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq35491
       grind)
    | exact superpose eq35491 eq9
    | exact resolve eq9 eq35491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35491
  have eq35874 : x = y ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq35783
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq35783
    | exact resolve eq35783 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35783
  have eq36511 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35874
       grind)
    | exact superpose eq35874 eq16
    | exact resolve eq16 eq35874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35874
  have eq36551 : y = (k y x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq36511
       have r₂ := eq323 x
       grind)
    | exact resolve eq36511 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36511
  have eq37177 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq36551
       have i₂ := eq1449 x y
       grind)
    | exact superpose eq1449 eq36551
    | (have j1 := eq1449 x y
       grind)
    | exact resolve eq36551 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq37198 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq37177
  have eq37204 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq37198
       have i₂ := eq10 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq10 eq37198
    | exact resolve eq37198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37198
  have eq37207 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have j1 := eq1461 y x
       grind)
    | (have r₁ := eq37204
       have r₂ := eq1461 y x
       grind)
    | exact resolve eq37204 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37204
  have eq37210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq37207
       have i₂ := eq10 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq10 eq37207
    | exact resolve eq37207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37207
  have eq37211 : (σ x) = (σ (M.op y y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq37210
       have r₂ := eq16
       grind)
    | exact resolve eq37210 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37210
  have eq37908 : (τ (σ x)) = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq37211
       grind)
    | exact superpose eq37211 eq9
    | exact resolve eq9 eq37211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37211
  have eq37997 : x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq37908
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq37908
    | exact resolve eq37908 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37908
  have eq38683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq37997
       grind)
    | exact superpose eq37997 eq417
    | exact resolve eq417 eq37997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37997
  have eq38720 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq38683
       have r₂ := eq16
       grind)
    | exact resolve eq38683 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38683
  have eq39418 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq38720
       grind)
    | exact superpose eq38720 eq10
    | exact resolve eq10 eq38720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38720
  have eq40224 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1461 y x
       have i₂ := eq39418
       grind)
    | exact superpose eq39418 eq1461
    | (have j0 := eq1461 y x
       grind)
    | (have r₁ := eq1461 y x
       have r₂ := eq39418
       grind)
    | exact resolve eq1461 eq39418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461 eq39418
  have eq40243 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq40224
  have eq40244 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq40243
  have eq41845 : (τ (σ x)) = (M.op y y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq40244
       grind)
    | exact superpose eq40244 eq9
    | exact resolve eq9 eq40244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40244
  have eq41936 : x = (M.op y y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq41845
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq41845
    | exact resolve eq41845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41845
  have eq42479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq41936
       grind)
    | exact superpose eq41936 eq417
    | exact resolve eq417 eq41936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41936
  have eq42516 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq42479
       have r₂ := eq16
       grind)
    | exact resolve eq42479 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42479
  have eq43175 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq42516
       grind)
    | exact superpose eq42516 eq9
    | exact resolve eq9 eq42516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43261 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq42516
  have eq43267 : y = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq43175
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq43175
    | exact resolve eq43175 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43175
  have eq44189 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq43267
       have i₂ := eq98 y x
       grind)
    | exact superpose eq98 eq43267
    | (have j1 := eq98 y x
       grind)
    | exact resolve eq43267 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq43267
  have eq44198 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq164 y x
       grind)
    | (have r₁ := eq44189
       have r₂ := eq164 y x
       grind)
    | exact resolve eq44189 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq44189
  have eq48615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq44198
       grind)
    | exact superpose eq44198 eq417
    | exact resolve eq417 eq44198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44198
  have eq48652 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq48615
       have r₂ := eq16
       grind)
    | exact resolve eq48615 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48615
  have eq49415 : (M.op x y) = (τ (σ x)) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq48652
       grind)
    | exact superpose eq48652 eq9
    | exact resolve eq9 eq48652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48652
  have eq49511 : x = (M.op x y) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq49415
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq49415
    | exact resolve eq49415 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49415
  have eq49817 : x ≠ x ∨ y = (k y x) ∨ x = (M.op y y) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq49511
       grind)
    | exact superpose eq49511 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq49511
       grind)
    | exact resolve eq12 eq49511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49511
  have eq49822 : x ≠ x ∨ y = (k y x) ∨ x = (M.op y y) ∨ x = (k y x) := by grind
  clear eq49817
  have eq49823 : x = (M.op y y) ∨ y = (k y x) ∨ x = (k y x) := by grind
  clear eq49822
  have eq50512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq49823
       grind)
    | exact superpose eq49823 eq417
    | exact resolve eq417 eq49823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49823
  have eq50549 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq50512
       have r₂ := eq16
       grind)
    | exact resolve eq50512 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50512
  have eq50803 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq349
       have i₂ := eq50549
       grind)
    | exact superpose eq50549 eq349
    | exact resolve eq349 eq50549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq50804 : x ≠ y ∨ x = (k y x) := by grind
  have eq50805 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (k y x) := by grind
  clear eq50803
  have eq65801 : y ≠ y ∨ x = (k y x) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq50805
       grind)
    | exact superpose eq50805 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq50805
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq50805
       grind)
    | exact resolve eq13 eq50805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50805
  have eq65809 : y ≠ y ∨ x = (k y x) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq65801
  have eq65810 : x = (k y x) ∨ x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq65809
  have eq65828 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq65810
       have r₂ := eq50804
       grind)
    | exact resolve eq65810 eq50804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65810
  have eq65869 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq65828
       grind)
    | exact superpose eq65828 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq65828
       grind)
    | exact resolve eq13 eq65828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65828
  have eq65872 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq65869
  have eq65889 : (σ x) = (σ (k y (τ (σ x)))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq65872
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq65872
    | exact resolve eq65872 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq65872
  have eq65900 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq65889
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq65889
    | exact resolve eq65889 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65889
  have eq65905 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq65900
       have r₂ := eq43261
       grind)
    | exact resolve eq65900 eq43261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43261 eq65900
  have eq65909 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op y y) ∨ x = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq65905
       have i₂ := eq323 y
       grind)
    | exact superpose eq323 eq65905
    | exact resolve eq65905 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65905
  have eq65910 : x = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k y x) := by grind
  clear eq65909
  have eq66001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq65910
       grind)
    | exact superpose eq65910 eq417
    | exact resolve eq417 eq65910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65910
  have eq66070 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq66001
       have r₂ := eq16
       grind)
    | exact resolve eq66001 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66001
  have eq66153 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq66070
       grind)
    | exact superpose eq66070 eq9
    | exact resolve eq9 eq66070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66070
  have eq66234 : x = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq66153
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq66153
    | exact resolve eq66153 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66153
  have eq66301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq66234
       grind)
    | exact superpose eq66234 eq417
    | exact resolve eq417 eq66234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66234
  have eq66375 : x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq66301
       have r₂ := eq16
       grind)
    | exact resolve eq66301 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66301
  have eq66429 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq66375
       have i₂ := eq36551
       grind)
    | exact superpose eq36551 eq66375
    | exact resolve eq66375 eq36551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36551
  have eq66435 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq66375
       have i₂ := eq50549
       grind)
    | exact superpose eq50549 eq66375
    | exact resolve eq66375 eq50549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50549 eq66375
  have eq66465 : (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq66435
       have r₂ := eq50804
       grind)
    | exact resolve eq66435 eq50804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66435
  have eq66535 : y = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq66465
       grind)
    | exact superpose eq66465 eq9
    | exact resolve eq9 eq66465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66465
  have eq66636 : x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq66535
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq66535
    | exact resolve eq66535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66535
  have eq66640 : x = (k y x) := by
    first
    | (have r₁ := eq66636
       have r₂ := eq50804
       grind)
    | exact resolve eq66636 eq50804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50804 eq66636
  have eq69244 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq66429
       have i₂ := eq66640
       grind)
    | exact superpose eq66640 eq66429
    | exact resolve eq66429 eq66640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66429
  have eq69254 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq69244
  have eq69284 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq69254
       have i₂ := eq66640
       grind)
    | exact superpose eq66640 eq69254
    | exact resolve eq69254 eq66640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69254
  have eq72800 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69284
       grind)
    | exact superpose eq69284 eq16
    | exact resolve eq16 eq69284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69284
  have eq72805 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq72800
       have r₂ := eq323 x
       grind)
    | exact resolve eq72800 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72800
  have eq72813 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq72805
       grind)
    | exact superpose eq72805 eq9
    | exact resolve eq9 eq72805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72805
  have eq72922 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72813
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq72813
    | exact resolve eq72813 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72813
  have eq72981 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72922
       grind)
    | exact superpose eq72922 eq16
    | exact resolve eq16 eq72922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72922
  have eq72990 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq72981
       have r₂ := eq323 x
       grind)
    | exact resolve eq72981 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72981
  have eq73339 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq72990
       grind)
    | exact superpose eq72990 eq9
    | exact resolve eq9 eq72990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72990
  have eq73454 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73339
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq73339
    | exact resolve eq73339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73339
  have eq73472 : x ≠ x ∨ y = (k y x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq73454
       grind)
    | exact superpose eq73454 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq73454
       grind)
    | exact resolve eq12 eq73454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73454
  have eq73494 : y = (k y x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq73472
  have eq73501 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73494
       have i₂ := eq66640
       grind)
    | exact superpose eq66640 eq73494
    | exact resolve eq73494 eq66640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66640 eq73494
  have eq73526 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73501
       grind)
    | exact superpose eq73501 eq16
    | exact resolve eq16 eq73501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73501
  have eq73543 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq73526
       have r₂ := eq323 x
       grind)
    | exact resolve eq73526 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq73526
  have eq73627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq73543
       grind)
    | exact superpose eq73543 eq417
    | exact resolve eq417 eq73543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73543
  have eq73696 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq73627
       have r₂ := eq16
       grind)
    | exact resolve eq73627 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73627
  have eq74187 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq417 y
       have i₂ := eq73696
       grind)
    | exact superpose eq73696 eq417
    | exact resolve eq417 eq73696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq74201 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq73696
       grind)
    | exact superpose eq73696 eq9
    | exact resolve eq9 eq73696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73696
  have eq74319 : x = (M.op y y) := by
    first
    | (have i₁ := eq74201
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq74201
    | exact resolve eq74201 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74201
  have eq74415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74187
       have i₂ := eq74319
       grind)
    | exact superpose eq74319 eq74187
    | exact resolve eq74187 eq74319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74187 eq74319
  have eq74621 : False := by grind
  exact eq74621

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_pxx_pxy_pyx_pyx_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (k X0 X0) X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq28 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1038 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1052 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1053 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1055 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1053 X0
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq1053 x
       have r₂ := eq14 x x
       grind)
    | (have r₁ := eq1053 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1053 X0
       have r₂ := eq14 X0 (k X0 X0)
       grind)
    | exact resolve eq1053 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1057 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq1055 X0
       grind)
    | exact superpose eq1055 eq176
    | exact resolve eq176 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1058 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq1055 X0
       grind)
    | exact superpose eq1055 eq175
    | exact resolve eq175 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1060 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq1055 X0
       grind)
    | exact superpose eq1055 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | (have r₁ := eq14 X0 (k X0 X0)
       have r₂ := eq1055 X0
       grind)
    | exact resolve eq14 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1057 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1057
    | exact resolve eq1057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1062 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq1062
    | exact resolve eq1062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1069 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1058 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1058
    | exact resolve eq1058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1074 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1069 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1069
    | exact resolve eq1069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq2378 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq41
    | exact resolve eq41 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq2379 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2378
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2378
    | exact resolve eq2378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2381 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2379
    | exact resolve eq2379 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq2383 : x = (k y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2381
       have i₂ := eq1055 y
       grind)
    | exact superpose eq1055 eq2381
    | exact resolve eq2381 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381
  have eq2385 : (M.op x y) = (k x x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2383
       have i₂ := eq1055 x
       grind)
    | exact superpose eq1055 eq2383
    | exact resolve eq2383 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2387 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2385
       have i₂ := eq1055 x
       grind)
    | exact superpose eq1055 eq2385
    | exact resolve eq2385 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq6423 : (M.op x y) ≠ (k x x) ∨ x = (M.op y y) ∨ y = (k x x) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq1055 x
       grind)
    | exact superpose eq1055 eq1050
    | exact resolve eq1050 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq6424 : (M.op x y) ≠ (k x x) ∨ x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq6423
       have i₂ := eq1055 y
       grind)
    | exact superpose eq1055 eq6423
    | exact resolve eq6423 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6425 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1051
       have i₂ := eq1055 sF2
       grind)
    | exact superpose eq1055 eq1051
    | exact resolve eq1051 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq6426 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6425
       have i₂ := eq1055 sF3
       grind)
    | exact superpose eq1055 eq6425
    | exact resolve eq6425 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6425
  have eq19025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq2387 eq1039
    | exact resolve eq1039 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19032 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq19025
       have r₂ := eq27
       grind)
    | exact resolve eq19025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19025
  have eq19038 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19032
       have i₂ := eq1055 sF3
       grind)
    | exact superpose eq1055 eq19032
    | exact resolve eq19032 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19032
  have eq19040 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19038
       have i₂ := eq1055 sF2
       grind)
    | exact superpose eq1055 eq19038
    | exact resolve eq19038 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19038
  have eq19042 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19040
       have i₂ := eq1055 sF2
       grind)
    | exact superpose eq1055 eq19040
    | exact resolve eq19040 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19040
  have eq19063 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by grind
  have eq19140 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq19042 eq6426
    | (have r₁ := eq6426
       have r₂ := eq19042
       grind)
    | exact resolve eq6426 eq19042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426 eq19042
  have eq19141 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by grind
  clear eq19140
  have eq19142 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by grind
  clear eq19141
  have eq19143 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq19142
       have r₂ := eq19063
       grind)
    | exact resolve eq19142 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19063 eq19142
  have eq19144 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq2387 eq19143
    | exact resolve eq19143 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387 eq19143
  have eq19145 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq19144
       have r₂ := eq27
       grind)
    | exact resolve eq19144 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19144
  have eq19149 : (τ (σ y)) = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq19145 eq98
    | exact resolve eq98 eq19145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq19145
  have eq19177 : y = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq19149
    | exact resolve eq19149 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19149
  have eq19178 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (k y y) := by grind
  clear eq19177
  have eq19193 : (τ (σ x)) = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq19178 eq116
    | exact resolve eq116 eq19178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19178
  have eq19222 : x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq19193
    | exact resolve eq19193 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19193
  have eq19223 : (M.op x y) = (k x x) ∨ y = (k x x) ∨ x = (k y y) := by grind
  clear eq19222
  have eq19235 : (M.op x y) ≠ (M.op x y) ∨ x = (k y y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq6424
       have i₂ := eq19223
       grind)
    | exact superpose eq19223 eq6424
    | (have r₁ := eq6424
       have r₂ := eq19223
       grind)
    | exact resolve eq6424 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6424
  have eq19239 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq19223
       grind)
    | exact superpose eq19223 eq40
    | exact resolve eq40 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19254 : y ≠ (M.op x y) ∨ y = (k x x) ∨ x = (k y y) := by grind
  clear eq19223
  have eq19255 : (M.op x y) ≠ (M.op x y) ∨ x = (k y y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x x) := by grind
  clear eq19235
  have eq19256 : x = (k y y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x x) := by grind
  clear eq19255
  have eq19264 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19239
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19239
    | exact resolve eq19239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19239
  have eq19268 : (M.op x y) = (k x y) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq19256
       have r₂ := eq19254
       grind)
    | exact resolve eq19256 eq19254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19256
  have eq19275 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq19264
    | exact resolve eq19264 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19264
  have eq19288 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq19268
       grind)
    | exact superpose eq19268 eq41
    | exact resolve eq41 eq19268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq19268
  have eq19289 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19288
    | exact resolve eq19288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19288
  have eq19293 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq19289
    | exact resolve eq19289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19289
  have eq19343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq19293 eq1039
    | exact resolve eq1039 eq19293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq19293
  have eq19350 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq19343
       have r₂ := eq27
       grind)
    | exact resolve eq19343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19343
  have eq19356 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19350
       have i₂ := eq1055 sF3
       grind)
    | exact superpose eq1055 eq19350
    | exact resolve eq19350 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19350
  have eq19358 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19356
       have i₂ := eq1055 sF2
       grind)
    | exact superpose eq1055 eq19356
    | exact resolve eq19356 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19356
  have eq19360 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19358
       have i₂ := eq1055 sF2
       grind)
    | exact superpose eq1055 eq19358
    | exact resolve eq19358 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq19358
  have eq19362 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq19275 eq19360
    | exact resolve eq19360 eq19275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19360
  have eq19364 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq19275 eq19362
    | exact resolve eq19362 eq19275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19275 eq19362
  have eq19366 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq19364
       have r₂ := eq27
       grind)
    | exact resolve eq19364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19364
  have eq19401 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq19366 eq116
    | exact resolve eq116 eq19366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq19366
  have eq19428 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq30 eq19401
    | exact resolve eq19401 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19401
  have eq19429 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by grind
  clear eq19428
  have eq19449 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1057 x
       have i₂ := eq19429
       grind)
    | exact superpose eq19429 eq1057
    | exact resolve eq1057 eq19429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19454 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1068 x
       have i₂ := eq19429
       grind)
    | exact superpose eq19429 eq1068
    | exact resolve eq1068 eq19429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068 eq19429
  have eq19470 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19454
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq19454
    | exact resolve eq19454 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19454
  have eq19472 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq1060 y x
       grind)
    | (have r₁ := eq19449
       have r₂ := eq1060 y x
       grind)
    | exact resolve eq19449 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19449
  have eq19482 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19470
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19470
    | exact resolve eq19470 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19470
  have eq19483 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19472
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19472
    | exact resolve eq19472 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19472
  have eq19489 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19482
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19482
    | exact resolve eq19482 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19482
  have eq19493 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq19489
    | exact resolve eq19489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19489
  have eq19497 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq19483
       grind)
    | exact superpose eq19483 eq40
    | exact resolve eq40 eq19483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19483
  have eq19498 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19497
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19497
    | exact resolve eq19497 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19497
  have eq19502 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq19498
    | exact resolve eq19498 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498
  have eq19571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | exact superpose eq19493 eq19502
    | exact resolve eq19502 eq19493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19493
  have eq19577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by grind
  clear eq19571
  have eq19584 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq19577
       have r₂ := eq27
       grind)
    | exact resolve eq19577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577
  have eq19599 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1074 y
       have i₂ := eq19584
       grind)
    | exact superpose eq19584 eq1074
    | exact resolve eq1074 eq19584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19584
  have eq19610 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19599
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq19599
    | exact resolve eq19599 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19599
  have eq19622 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19610
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19610
    | exact resolve eq19610 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19610
  have eq19628 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19622
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19622
    | exact resolve eq19622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19622
  have eq19632 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq19628
    | exact resolve eq19628 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19628
  have eq19635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19502 eq19632
    | exact resolve eq19632 eq19502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19502 eq19632
  have eq19636 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq19635
       have r₂ := eq27
       grind)
    | exact resolve eq19635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19635
  have eq19637 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq19636 eq29
    | exact resolve eq29 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq20016 : y = (M.op x y) := by
    first
    | exact superpose eq19637 eq32
    | exact resolve eq32 eq19637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19637
  have eq20105 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20016
       grind)
    | exact superpose eq20016 eq18
    | exact resolve eq18 eq20016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20125 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19254
       have i₂ := eq20016
       grind)
    | exact superpose eq20016 eq19254
    | (have r₁ := eq19254
       have r₂ := eq20016
       grind)
    | exact resolve eq19254 eq20016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254 eq20016
  have eq20130 : (M.op x y) = (k x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq20125
  have eq22536 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20130
       grind)
    | exact superpose eq20130 eq40
    | exact resolve eq40 eq20130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22537 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1057 x
       have i₂ := eq20130
       grind)
    | exact superpose eq20130 eq1057
    | exact resolve eq1057 eq20130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20130
  have eq22564 : (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have j1 := eq1060 (M.op x y) x
       grind)
    | (have r₁ := eq22537
       have r₂ := eq1060 (M.op x y) x
       grind)
    | exact resolve eq22537 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq22537
  have eq22565 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22536
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22536
    | exact resolve eq22536 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22536
  have eq22575 : (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq20105 eq22564
    | exact resolve eq22564 eq20105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20105 eq22564
  have eq22576 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq22565
    | exact resolve eq22565 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22565
  have eq22586 : (σ y) = (k (σ x) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19636 eq22576
    | exact resolve eq22576 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576
  have eq22606 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq22575 eq40
    | exact resolve eq40 eq22575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22575
  have eq22608 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq22606
    | exact resolve eq22606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22606
  have eq22614 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq19636 eq22608
    | exact resolve eq22608 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22608
  have eq22675 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22586 eq1057
    | exact resolve eq1057 eq22586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq22586
  have eq22699 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22614 eq22675
    | exact resolve eq22675 eq22614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22675
  have eq22709 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22699
    | exact resolve eq22699 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22699
  have eq22740 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22709 eq1074
    | exact resolve eq1074 eq22709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq22709
  have eq22756 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22740
    | exact resolve eq22740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22740
  have eq22771 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19636 eq22756
    | exact resolve eq22756 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22756
  have eq22784 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22771
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22771
    | exact resolve eq22771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22771
  have eq22793 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22784
       have i₂ := eq40 sF0
       grind)
    | exact superpose eq40 eq22784
    | exact resolve eq22784 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq22784
  have eq22799 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22793
    | exact resolve eq22793 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22793
  have eq22804 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19636 eq22799
    | exact resolve eq22799 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22799
  have eq22807 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22614 eq22804
    | exact resolve eq22804 eq22614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22614 eq22804
  have eq22808 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22807
    | exact resolve eq22807 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22807
  have eq22809 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22808
  have eq22810 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq22809 eq27
    | exact resolve eq27 eq22809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22809
  have eq22820 : False := by grind
  exact eq22820

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_pxy_pyx_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (k X0 X0) X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq29 (M.op X1 X1) X1
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq29 X1 X1
       have r₂ := eq28 (k X1 X1) X1
       grind)
    | exact resolve eq29 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq100 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq118 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq177 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq28 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1053 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1049 X0 X1
       have i₂ := eq1041 X1
       grind)
    | exact superpose eq1041 eq1049
    | (have j0 := eq1049 X0 X1
       grind)
    | (have r₁ := eq1049 X0 X0
       have r₂ := eq1041 X0
       grind)
    | exact resolve eq1049 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1057 : (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq1041 sF3
       grind)
    | exact superpose eq1041 eq1043
    | exact resolve eq1043 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1058 : x = (k y y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1042
       have i₂ := eq1041 y
       grind)
    | exact superpose eq1041 eq1042
    | exact resolve eq1042 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1059 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1053 X0 X1
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq1053
    | (have j0 := eq1053 X0 X1
       grind)
    | (have r₁ := eq1053 X0 X0
       have r₂ := eq1041 X0
       grind)
    | exact resolve eq1053 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1063 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1057
       have i₂ := eq1041 sF2
       grind)
    | exact superpose eq1041 eq1057
    | exact resolve eq1057 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1064 : (M.op x y) = (k x y) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq1041 x
       grind)
    | exact superpose eq1041 eq1058
    | exact resolve eq1058 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1067 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq178
    | exact resolve eq178 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1068 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq177
    | exact resolve eq177 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1069 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq28
    | (have j0 := eq28 X1 X0
       grind)
    | (have r₁ := eq28 (k X0 X0) X0
       have r₂ := eq1041 X0
       grind)
    | exact resolve eq28 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | (have r₁ := eq14 X0 (k X0 X0)
       have r₂ := eq1041 X0
       grind)
    | exact resolve eq14 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1071 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1067 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1067
    | exact resolve eq1067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1076 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1071 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq1071
    | exact resolve eq1071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1077 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1068 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1068
    | exact resolve eq1068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1083 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1077 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1077
    | exact resolve eq1077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq2392 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq43
    | exact resolve eq43 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq2393 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2392
    | exact resolve eq2392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2395 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq2393
    | exact resolve eq2393 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq6408 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X0) = X1 ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1059 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq1059
    | (have j0 := eq1059 X1 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq1059 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq1059 X1 X1
       have r₂ := eq11 (k X1 X1) X1
       grind)
    | (have r₁ := eq1059 X0 X0
       have r₂ := eq11 X0 (k X0 X0)
       grind)
    | exact resolve eq1059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq6415 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6408 X0 X1
       have j1 := eq1070 X0 X1
       grind)
    | (have r₁ := eq6408 X0 X1
       have r₂ := eq1070 X0 X1
       grind)
    | (have r₁ := eq6408 X0 (k X0 X0)
       have r₂ := eq1070 X0 (k X0 X0)
       grind)
    | (have r₁ := eq6408 X1 X0
       have r₂ := eq1070 X0 X1
       grind)
    | exact resolve eq6408 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408
  have eq6416 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq6415 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq6415 (M.op X0 X0) X1
       have r₂ := eq14 X0 (k X1 X1)
       grind)
    | (have r₁ := eq6415 X0 X0
       have r₂ := eq14 X0 (k X0 X0)
       grind)
    | (have r₁ := eq6415 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq6415 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6415
  have eq6417 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq6416 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq6416 (M.op X1 X1) X1
       have r₂ := eq28 (k X1 X1) X1
       grind)
    | (have r₁ := eq6416 X1 X1
       have r₂ := eq28 (k X1 X1) X1
       grind)
    | (have r₁ := eq6416 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq6416 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6416
  have eq6418 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq6417 X0 X1
       have j1 := eq30 X0 X1
       grind)
    | (have r₁ := eq6417 X0 X1
       have r₂ := eq30 X0 X1
       grind)
    | (have r₁ := eq6417 X1 X0
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq6417 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6417
  have eq6419 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq6418 X0 X1
       have j1 := eq1069 X1 X0
       grind)
    | (have r₁ := eq6418 X1 X0
       have r₂ := eq1069 X0 X1
       grind)
    | (have r₁ := eq6418 (k X0 X0) X1
       have r₂ := eq1069 X0 (k X1 X1)
       grind)
    | (have r₁ := eq6418 X0 X0
       have r₂ := eq1069 X0 (M.op X0 X0)
       grind)
    | exact resolve eq6418 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418
  have eq19292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2395 eq1063
    | exact resolve eq1063 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq19299 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19292
       have r₂ := eq27
       grind)
    | exact resolve eq19292 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19292
  have eq19309 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19299 eq30
    | (have r₁ := eq30 (σ y) (σ x)
       have r₂ := eq19299
       grind)
    | (have r₁ := eq30 (σ x) (σ y)
       have r₂ := eq19299
       grind)
    | (have r₁ := eq30 y x
       have r₂ := eq19299
       grind)
    | exact resolve eq30 eq19299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19299
  have eq19311 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19309
       have r₂ := eq26
       grind)
    | exact resolve eq19309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19309
  have eq19315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2395 eq19311
    | exact resolve eq19311 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395 eq19311
  have eq19318 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq19315
       have r₂ := eq27
       grind)
    | exact resolve eq19315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19315
  have eq19357 : (τ (σ y)) = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19318 eq100
    | exact resolve eq100 eq19318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq19318
  have eq19392 : y = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq34 eq19357
    | exact resolve eq19357 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq19357
  have eq19393 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq19392
  have eq19408 : (τ (σ x)) = (k y y) ∨ y = (k x x) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq19393 eq118
    | exact resolve eq118 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq19393
  have eq19443 : x = (k y y) ∨ y = (k x x) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq32 eq19408
    | exact resolve eq19408 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19408
  have eq19444 : (M.op x y) = (M.op y x) ∨ y = (k x x) ∨ x = (k y y) := by grind
  clear eq19443
  have eq19458 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq30 y x
       have i₂ := eq19444
       grind)
    | exact superpose eq19444 eq30
    | (have j0 := eq30 y x
       grind)
    | (have r₁ := eq30 y x
       have r₂ := eq19444
       grind)
    | (have r₁ := eq30 x y
       have r₂ := eq19444
       grind)
    | exact resolve eq30 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19459 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq30 x y
       have i₂ := eq19444
       grind)
    | exact superpose eq19444 eq30
    | (have r₁ := eq30 y x
       have r₂ := eq19444
       grind)
    | (have r₁ := eq30 x y
       have r₂ := eq19444
       grind)
    | exact resolve eq30 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19444
  have eq19461 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq19459
       have r₂ := eq18
       grind)
    | exact resolve eq19459 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19459
  have eq19462 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k y y) := by
    first
    | (have j1 := eq1069 x y
       grind)
    | (have r₁ := eq19458
       have r₂ := eq1069 x y
       grind)
    | (have r₁ := eq19458
       have r₂ := eq1069 y x
       grind)
    | exact resolve eq19458 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069 eq19458
  have eq19465 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq1070 y x
       grind)
    | (have r₁ := eq19462
       have r₂ := eq1070 y x
       grind)
    | exact resolve eq19462 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq19462
  have eq19467 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq19465
       have r₂ := eq18
       grind)
    | exact resolve eq19465 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19465
  have eq19468 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq19467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19467
    | exact resolve eq19467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19467
  have eq19477 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq19468
       grind)
    | exact superpose eq19468 eq42
    | exact resolve eq42 eq19468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19468
  have eq19481 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19477
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19477
    | exact resolve eq19477 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19477
  have eq19485 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq19481
    | exact resolve eq19481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19481
  have eq19496 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19485 eq6419
    | exact resolve eq6419 eq19485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6419
  have eq19497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19496
    | exact resolve eq19496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19496
  have eq19503 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq19497
       have r₂ := eq27
       grind)
    | exact resolve eq19497 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19497
  have eq19642 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq19461
       grind)
    | exact superpose eq19461 eq43
    | exact resolve eq43 eq19461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq19461
  have eq19645 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19642
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19642
    | exact resolve eq19642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19642
  have eq19649 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq19645
    | exact resolve eq19645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19645
  have eq19651 : y = (k x x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq19649
       have r₂ := eq19503
       grind)
    | exact resolve eq19649 eq19503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19503 eq19649
  have eq19662 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1076 x
       have i₂ := eq19651
       grind)
    | exact superpose eq19651 eq1076
    | exact resolve eq1076 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq19651
  have eq19682 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19662
       have i₂ := eq42 y
       grind)
    | exact superpose eq42 eq19662
    | exact resolve eq19662 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19662
  have eq19695 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19682
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19682
    | exact resolve eq19682 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19682
  have eq19702 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq19695
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19695
    | exact resolve eq19695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19695
  have eq19706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq19485 eq19702
    | exact resolve eq19702 eq19485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19702
  have eq19708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq19706
    | exact resolve eq19706 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19706
  have eq19709 : x = (k y y) := by
    first
    | (have r₁ := eq19708
       have r₂ := eq27
       grind)
    | exact resolve eq19708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19708
  have eq19721 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1083 y
       have i₂ := eq19709
       grind)
    | exact superpose eq19709 eq1083
    | exact resolve eq1083 eq19709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq19709
  have eq19738 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19721
       have i₂ := eq42 y
       grind)
    | exact superpose eq42 eq19721
    | exact resolve eq19721 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq19721
  have eq19750 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19738
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19738
    | exact resolve eq19738 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19738
  have eq19756 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19750
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19750
    | exact resolve eq19750 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19750
  have eq19760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19485 eq19756
    | exact resolve eq19756 eq19485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19485 eq19756
  have eq19811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19760 eq26
    | exact resolve eq26 eq19760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19760
  have eq19815 : False := by grind
  exact eq19815

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_pxy_y_pyx_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    grind
  have eq41 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 (τ (M.op (σ X0) (σ X0))))
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq56 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq61 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (M.op (σ x) (σ y)) = (σ (k x (τ (σ y)))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq20 (σ y) x
       grind)
    | exact superpose eq20 eq56
    | exact resolve eq56 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq71 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq20
    | (have j1 := eq63 (σ X0)
       grind)
    | exact resolve eq20 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq23
    | (have j1 := eq63 (τ X0)
       grind)
    | exact resolve eq23 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X0
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq67
    | (have j0 := eq67 X1 (σ X0)
       grind)
    | exact resolve eq67 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (τ X0)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq67
    | (have j0 := eq67 X1 (τ X0)
       grind)
    | exact resolve eq67 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq98 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq98
  have eq124 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 X1 (σ X0)
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq168 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq76
  have eq169 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq168 X0
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq168
    | (have j0 := eq168 X0
       grind)
    | exact resolve eq168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq171 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq169 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169
    | (have j0 := eq169 X0
       grind)
    | exact resolve eq169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq172 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq178 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq41
    | (have j1 := eq92 X0
       grind)
    | exact resolve eq41 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq92
  have eq182 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq178
    | (have j0 := eq178 X0
       grind)
    | exact resolve eq178 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq183 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq186 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq63
    | (have j0 := eq63 X0
       grind)
    | exact resolve eq63 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq192 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq172
    | exact resolve eq172 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq197 : ∀ X0 X1 : G, (τ (τ (M.op (σ X0) (σ X0)))) = X1 ∨ (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq244 : ∀ X0 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq183 (τ X0)
       grind)
    | exact superpose eq183 eq23
    | exact resolve eq23 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq244 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq244
    | exact resolve eq244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq252 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq247 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq247
    | exact resolve eq247 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq257 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq192 X0
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq192
    | exact resolve eq192 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq258 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq197
    | (have j0 := eq197 X0 X1
       grind)
    | exact resolve eq197 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq252
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    grind
  clear eq186
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq279 X0
       grind)
    | exact superpose eq279 eq183
    | exact resolve eq183 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq279
  have eq289 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq280 (σ X0)
       grind)
    | exact superpose eq280 eq20
    | exact resolve eq20 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq289
    | exact resolve eq289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq297 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq292
    | exact resolve eq292 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq292
  have eq303 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq314 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq297 x
       grind)
    | exact superpose eq297 eq99
    | exact resolve eq99 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq315 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq297 x
       grind)
    | exact superpose eq297 eq71
    | exact resolve eq71 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq316 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq315
       have i₂ := eq297 y
       grind)
    | exact superpose eq297 eq315
    | exact resolve eq315 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq317 : (M.op x y) = (k x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq314
       have i₂ := eq297 y
       grind)
    | exact superpose eq297 eq314
    | exact resolve eq314 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq320 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq297 X1
       grind)
    | exact superpose eq297 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq325 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq326 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  have eq333 : ∀ X0 : G, (τ (k X0 (σ (τ (M.op X0 X0))))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq23 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq23 eq326
    | exact resolve eq326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq334 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq325
    | (have j0 := eq325 X0
       grind)
    | exact resolve eq325 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq336 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq333
    | exact resolve eq333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq337 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq334
    | (have j0 := eq334 X0
       grind)
    | exact resolve eq334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq338 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq336
  have eq339 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq257 (M.op X0 X0)
       grind)
    | exact superpose eq257 eq337
    | (have j0 := eq337 X0
       grind)
    | exact resolve eq337 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq373 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq374 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq381 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq20 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq20 eq374
    | exact resolve eq374 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq382 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq373
    | (have j0 := eq373 X0
       grind)
    | exact resolve eq373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq384 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq381
    | exact resolve eq381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq385 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq382 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq382
    | (have j0 := eq382 X0
       grind)
    | exact resolve eq382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq386 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq384
  have eq387 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq297 (M.op X0 X0)
       grind)
    | exact superpose eq297 eq385
    | (have j0 := eq385 X0
       grind)
    | exact resolve eq385 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq445 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (σ X1))
       have i₂ := eq258 X0 X1
       grind)
    | exact superpose eq258 eq10
    | (have j1 := eq258 X0 X1
       grind)
    | exact resolve eq10 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq320 y x
       have i₂ := eq317
       grind)
    | exact superpose eq317 eq320
    | (have j0 := eq320 y x
       grind)
    | exact resolve eq320 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq320
  have eq606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq595
  have eq608 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq606
       have r₂ := eq16
       grind)
    | exact resolve eq606 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq612 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq608
       have r₂ := eq316
       grind)
    | exact resolve eq608 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq608
  have eq1107 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq10
    | (have j1 := eq339 X0
       grind)
    | exact resolve eq10 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq1124 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1107 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1107
    | (have j0 := eq1107 X0
       grind)
    | exact resolve eq1107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1168 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) = (τ (k (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1124 (τ X0)
       have i₂ := eq257 X0
       grind)
    | exact superpose eq257 eq1124
    | exact resolve eq1124 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq338 (M.op X0 X0)
       have i₂ := eq1124 X0
       grind)
    | exact superpose eq1124 eq338
    | (have j1 := eq1124 X0
       grind)
    | exact resolve eq338 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq1173 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq386 (M.op X0 X0)
       have i₂ := eq1124 X0
       grind)
    | exact superpose eq1124 eq386
    | (have j1 := eq1124 X0
       grind)
    | exact resolve eq386 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1186 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) = (τ (k (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq257 (M.op X0 X0)
       grind)
    | exact superpose eq257 eq1168
    | (have j0 := eq1168 X0
       grind)
    | exact resolve eq1168 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1188 : ∀ X0 : G, (τ (τ (k (M.op X0 X0) (σ (τ X0))))) = (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1186 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq1186
    | (have j0 := eq1186 X0
       grind)
    | exact resolve eq1186 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1190 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (τ (k (M.op X0 X0) X0))) = (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1188 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1188
    | (have j0 := eq1188 X0
       grind)
    | exact resolve eq1188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1195 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq445
    | (have j0 := eq445 X1 (τ X0)
       grind)
    | exact resolve eq445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq1233 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1195 X0 X1
       have i₂ := eq257 X0
       grind)
    | exact superpose eq257 eq1195
    | (have j0 := eq1195 X0 X1
       grind)
    | exact resolve eq1195 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1397 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq9
    | (have j1 := eq387 X0
       grind)
    | exact resolve eq9 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq1415 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1397 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1397
    | (have j0 := eq1397 X0
       grind)
    | exact resolve eq1397 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1475 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq386 (M.op X0 X0)
       have i₂ := eq1415 X0
       grind)
    | exact superpose eq1415 eq386
    | (have j1 := eq1415 X0
       grind)
    | exact resolve eq386 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq3858 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1172 (σ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq1172
    | exact resolve eq1172 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq3874 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (σ X0)) (M.op X0 X0)) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3858 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3858
    | (have j0 := eq3858 X0
       grind)
    | exact resolve eq3858 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858
  have eq3881 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3874 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3874
    | (have j0 := eq3874 X0
       grind)
    | exact resolve eq3874 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq3885 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3881 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3881
    | (have j0 := eq3881 X0
       grind)
    | exact resolve eq3881 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3881
  have eq3889 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3885 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3885
    | (have j0 := eq3885 X0
       grind)
    | exact resolve eq3885 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq3893 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (σ (k (M.op X0 X0) (τ (σ X0))))) ∨ (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3889 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq3889
    | (have j0 := eq3889 X0
       grind)
    | exact resolve eq3889 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq3895 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) (τ (σ X0))) ∨ (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3893 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq3893
    | (have j0 := eq3893 X0
       grind)
    | exact resolve eq3893 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq3897 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3895 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3895
    | (have j0 := eq3895 X0
       grind)
    | exact resolve eq3895 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq4012 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ (M.op X0 X0)))
       have i₂ := eq3897 X0
       grind)
    | exact superpose eq3897 eq10
    | (have j1 := eq3897 X0
       grind)
    | exact resolve eq10 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq4362 : ∀ X0 : G, (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) = (σ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1173 (σ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq1173
    | exact resolve eq1173 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq4384 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (M.op X0 X0)) ∨ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) = (σ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4362 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq4362
    | (have j0 := eq4362 X0
       grind)
    | exact resolve eq4362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362
  have eq4392 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) = (σ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4384 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4384
    | (have j0 := eq4384 X0
       grind)
    | exact resolve eq4384 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4384
  have eq4400 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (σ (k (M.op X0 X0) (τ (σ X0))))) ∨ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) = (σ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4392 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq4392
    | (have j0 := eq4392 X0
       grind)
    | exact resolve eq4392 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4408 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) (τ (σ X0))) ∨ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) = (σ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4400 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq4400
    | (have j0 := eq4400 X0
       grind)
    | exact resolve eq4400 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4400
  have eq4415 : ∀ X0 : G, (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) = (σ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4408 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4408
    | (have j0 := eq4408 X0
       grind)
    | exact resolve eq4408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4408
  have eq4533 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (τ (τ (k (M.op X0 X0) X0))) = (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq1190 X0
       grind)
    | exact superpose eq1190 eq10
    | (have j1 := eq1190 X0
       grind)
    | exact resolve eq10 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq4562 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (τ (τ (k (M.op X0 X0) X0))) = (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4533 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4533
    | (have j0 := eq4533 X0
       grind)
    | exact resolve eq4533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533
  have eq4703 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (τ (τ (k (M.op X0 X0) X0))) = (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq4562
  have eq11351 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (τ (τ (k (σ (M.op X0 X0)) (σ X0)))) = (M.op (τ (τ (σ X0))) (τ (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq4703 (σ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq4703
    | exact resolve eq4703 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq11433 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) (τ (σ X0)))) ∨ (τ (τ (k (σ (M.op X0 X0)) (σ X0)))) = (M.op (τ (τ (σ X0))) (τ (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq11351 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq11351
    | (have j0 := eq11351 X0
       grind)
    | exact resolve eq11351 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11351
  have eq11463 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (τ (τ (k (σ (M.op X0 X0)) (σ X0)))) = (M.op (τ (τ (σ X0))) (τ (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq11433 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11433
    | (have j0 := eq11433 X0
       grind)
    | exact resolve eq11433 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11433
  have eq11492 : ∀ X0 : G, (τ (τ (k (σ (M.op X0 X0)) (σ X0)))) = (M.op (τ (τ (σ X0))) (τ (M.op X0 X0))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11463 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq11463
    | (have j0 := eq11463 X0
       grind)
    | exact resolve eq11463 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11463
  have eq11521 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (τ (k (σ (M.op X0 X0)) (σ X0)))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11492 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11492
    | (have j0 := eq11492 X0
       grind)
    | exact resolve eq11492 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11492
  have eq11545 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (τ (σ (k (M.op X0 X0) (τ (σ X0)))))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11521 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq11521
    | (have j0 := eq11521 X0
       grind)
    | exact resolve eq11521 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq11568 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) (τ (σ X0)))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11545 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq11545
    | (have j0 := eq11545 X0
       grind)
    | exact resolve eq11545 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11545
  have eq11587 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11568 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11568
    | (have j0 := eq11568 X0
       grind)
    | exact resolve eq11568 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11568
  have eq12412 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0)
       have i₂ := eq11587 X0
       grind)
    | exact superpose eq11587 eq9
    | (have j1 := eq11587 X0
       grind)
    | exact resolve eq9 eq11587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq12811 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12412 (σ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq12412
    | exact resolve eq12412 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12412
  have eq12917 : ∀ X0 : G, (σ (k (M.op X0 X0) (τ (σ X0)))) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12811 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12811
    | (have j0 := eq12811 X0
       grind)
    | exact resolve eq12811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12811
  have eq12951 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12917 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12917
    | (have j0 := eq12917 X0
       grind)
    | exact resolve eq12917 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12917
  have eq12981 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (M.op X0 X0)) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq12951 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12951
    | (have j0 := eq12951 X0
       grind)
    | exact resolve eq12951 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12951
  have eq13010 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq12981 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12981
    | (have j0 := eq12981 X0
       grind)
    | exact resolve eq12981 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12981
  have eq13039 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (σ (k (M.op X0 X0) (τ (σ X0))))) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq13010 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq13010
    | (have j0 := eq13010 X0
       grind)
    | exact resolve eq13010 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13010
  have eq13067 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) (τ (σ X0))) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq13039 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq13039
    | (have j0 := eq13039 X0
       grind)
    | exact resolve eq13039 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13039
  have eq13092 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13067 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13067
    | (have j0 := eq13067 X0
       grind)
    | exact resolve eq13067 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13067
  have eq13865 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1233 X0 X1
       grind)
    | exact superpose eq1233 eq10
    | (have j1 := eq1233 X0 X1
       grind)
    | exact resolve eq10 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq13912 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13865 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13865
    | (have j0 := eq13865 X0 X1
       grind)
    | exact resolve eq13865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13865
  have eq13977 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (τ (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0)
       have i₂ := eq13092 X0
       grind)
    | exact superpose eq13092 eq9
    | (have j1 := eq13092 X0
       grind)
    | exact resolve eq9 eq13092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13092
  have eq14417 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (k (τ (M.op X0 X0)) (τ X0)) = (τ (τ (M.op (σ (σ (τ X0))) (σ (σ (τ (M.op X0 X0))))))) := by
    intro X0
    first
    | (have i₁ := eq13977 (τ X0)
       have i₂ := eq257 X0
       grind)
    | exact superpose eq257 eq13977
    | exact resolve eq13977 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq13977
  have eq14509 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) (σ (τ X0)))) ∨ (k (τ (M.op X0 X0)) (τ X0)) = (τ (τ (M.op (σ (σ (τ X0))) (σ (σ (τ (M.op X0 X0))))))) := by
    intro X0
    first
    | (have i₁ := eq14417 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq14417
    | (have j0 := eq14417 X0
       grind)
    | exact resolve eq14417 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14417
  have eq14542 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (k (τ (M.op X0 X0)) (τ X0)) = (τ (τ (M.op (σ (σ (τ X0))) (σ (σ (τ (M.op X0 X0))))))) := by
    intro X0
    first
    | (have i₁ := eq14509 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14509
    | (have j0 := eq14509 X0
       grind)
    | exact resolve eq14509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14509
  have eq14574 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (τ (M.op (σ (σ (τ X0))) (σ (M.op X0 X0))))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14542 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq14542
    | (have j0 := eq14542 X0
       grind)
    | exact resolve eq14542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14542
  have eq14605 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (τ (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14574 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14574
    | (have j0 := eq14574 X0
       grind)
    | exact resolve eq14574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14574
  have eq14631 : ∀ X0 : G, (τ (k (M.op X0 X0) (σ (τ X0)))) = (τ (τ (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14605 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq14605
    | (have j0 := eq14605 X0
       grind)
    | exact resolve eq14605 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14605
  have eq14655 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (τ (k (M.op X0 X0) X0)) = (τ (τ (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq14631 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14631
    | (have j0 := eq14631 X0
       grind)
    | exact resolve eq14631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14631
  have eq14882 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13912 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq13912
    | (have j0 := eq13912 X1 (σ X0)
       grind)
    | exact resolve eq13912 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13912
  have eq14995 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14882 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14882
    | (have j0 := eq14882 X0 X1
       grind)
    | exact resolve eq14882 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14882
  have eq15032 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14995 X0 X1
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq14995
    | (have j0 := eq14995 X0 X1
       grind)
    | exact resolve eq14995 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq15054 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15032 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq15032
    | (have j0 := eq15032 X0 X1
       grind)
    | exact resolve eq15032 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15032
  have eq15067 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15054 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15054
    | (have j0 := eq15054 X0 X1
       grind)
    | exact resolve eq15054 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15054
  have eq25154 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15067 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15067
    | (have j0 := eq15067 X1 (σ X0)
       grind)
    | exact resolve eq15067 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15067
  have eq25351 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25154 X0 X1
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq25154
    | (have j0 := eq25154 X0 X1
       grind)
    | exact resolve eq25154 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25154
  have eq25365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25351 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq25351
    | (have j0 := eq25351 X0 X1
       grind)
    | exact resolve eq25351 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25351
  have eq34154 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (τ (τ (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq14655 X0
       grind)
    | exact superpose eq14655 eq10
    | (have j1 := eq14655 X0
       grind)
    | exact resolve eq10 eq14655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14655
  have eq35308 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (τ (τ (M.op (σ X0) (σ (M.op X0 X0)))))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq34154 X0
       grind)
    | exact superpose eq34154 eq10
    | (have j1 := eq34154 X0
       grind)
    | exact resolve eq10 eq34154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34154
  have eq35372 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq35308 X0
       have i₂ := eq10 (τ (M.op (σ X0) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq10 eq35308
    | (have j0 := eq35308 X0
       grind)
    | exact resolve eq35308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35308
  have eq36440 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq35372 (σ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq35372
    | exact resolve eq35372 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq35372
  have eq36620 : ∀ X0 : G, (σ (k (M.op X0 X0) (τ (σ X0)))) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq36440 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq36440
    | (have j0 := eq36440 X0
       grind)
    | exact resolve eq36440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36440
  have eq36681 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq36620 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36620
    | (have j0 := eq36620 X0
       grind)
    | exact resolve eq36620 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36620
  have eq36737 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq36681 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq36681
    | (have j0 := eq36681 X0
       grind)
    | exact resolve eq36681 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36681
  have eq36792 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq36737 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36737
    | (have j0 := eq36737 X0
       grind)
    | exact resolve eq36737 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36737
  have eq36846 : ∀ X0 : G, (σ (k (M.op X0 X0) (τ (σ X0)))) = (σ (M.op X0 (M.op X0 X0))) ∨ (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq36792 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq36792
    | (have j0 := eq36792 X0
       grind)
    | exact resolve eq36792 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36792
  have eq36897 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36846 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36846
    | (have j0 := eq36846 X0
       grind)
    | exact resolve eq36846 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36846
  have eq45020 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (τ (M.op (σ (σ X0)) (σ (σ (M.op X0 X0))))) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq36897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36897
  have eq46862 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (τ (σ (M.op (σ X0) (σ (M.op X0 X0))))) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45020 X0
       have i₂ := eq4415 X0
       grind)
    | exact superpose eq4415 eq45020
    | (have j0 := eq45020 X0
       have j1 := eq4415 X0
       grind)
    | exact resolve eq45020 eq4415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415 eq45020
  have eq46873 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46862 X0
       have i₂ := eq9 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq9 eq46862
    | (have j0 := eq46862 X0
       grind)
    | exact resolve eq46862 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46862
  have eq46916 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq46873 X0
       have j1 := eq4012 X0
       grind)
    | (have r₁ := eq46873 X0
       have r₂ := eq4012 X0
       grind)
    | exact resolve eq46873 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012 eq46873
  have eq48206 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op X0 (M.op X0 X0)))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0)
       have i₂ := eq46916 X0
       grind)
    | exact superpose eq46916 eq9
    | (have j1 := eq46916 X0
       grind)
    | exact resolve eq9 eq46916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46916
  have eq48269 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48206 X0
       have i₂ := eq9 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq48206
    | (have j0 := eq48206 X0
       grind)
    | exact resolve eq48206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48206
  have eq48270 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48269
  have eq48360 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1475 X0
       have i₂ := eq48270 X0
       grind)
    | exact superpose eq48270 eq1475
    | (have j0 := eq1475 X0
       grind)
    | exact resolve eq1475 eq48270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq48270
  have eq50390 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq48360 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48360
  have eq55141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq50390 x
       have i₂ := eq612
       grind)
    | exact superpose eq612 eq50390
    | exact resolve eq50390 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq55176 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq55141
       have r₂ := eq16
       grind)
    | exact resolve eq55141 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55141
  have eq62329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq386 y
       have i₂ := eq55176
       grind)
    | exact superpose eq55176 eq386
    | exact resolve eq386 eq55176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55176
  have eq62386 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq62329
       have r₂ := eq16
       grind)
    | exact resolve eq62329 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62329
  have eq62974 : (τ (σ y)) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq62386
       grind)
    | exact superpose eq62386 eq9
    | exact resolve eq9 eq62386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62386
  have eq63042 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq62974
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq62974
    | exact resolve eq62974 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62974
  have eq63276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq50390 x
       have i₂ := eq63042
       grind)
    | exact superpose eq63042 eq50390
    | exact resolve eq50390 eq63042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63042
  have eq63318 : (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq63276
       have r₂ := eq16
       grind)
    | exact resolve eq63276 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63276
  have eq63592 : (M.op y y) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq63318
       grind)
    | exact superpose eq63318 eq9
    | exact resolve eq9 eq63318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63318
  have eq63661 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq63592
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq63592
    | exact resolve eq63592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63592
  have eq63990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq386 y
       have i₂ := eq63661
       grind)
    | exact superpose eq63661 eq386
    | exact resolve eq386 eq63661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63661
  have eq64046 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq63990
       have r₂ := eq16
       grind)
    | exact resolve eq63990 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63990
  have eq64343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq64046
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq64046
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq64046 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq64369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25365 y x
       have i₂ := eq64046
       grind)
    | exact superpose eq64046 eq25365
    | (have j0 := eq25365 y x
       grind)
    | exact resolve eq25365 eq64046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25365
  have eq64370 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq64046
       grind)
    | exact superpose eq64046 eq9
    | exact resolve eq9 eq64046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64046
  have eq64498 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq64369
       have r₂ := eq16
       grind)
    | exact resolve eq64369 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64369
  have eq64517 : x = (M.op y y) ∨ y = (M.op x x) ∨ y = (k x y) := by
    first
    | (have r₁ := eq64343
       have r₂ := eq16
       grind)
    | exact resolve eq64343 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64343
  have eq64579 : y = (M.op x x) ∨ x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64517
       have i₂ := eq64370
       grind)
    | exact superpose eq64370 eq64517
    | exact resolve eq64517 eq64370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64517
  have eq65524 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64498
       grind)
    | exact superpose eq64498 eq16
    | exact resolve eq16 eq64498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64498
  have eq65908 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65524
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq65524
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq65524 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65918 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq65908
  have eq65919 : y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq65918
  have eq65920 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65919
       have i₂ := eq64370
       grind)
    | exact superpose eq64370 eq65919
    | exact resolve eq65919 eq64370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64370 eq65919
  have eq66165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq50390 x
       have i₂ := eq64579
       grind)
    | exact superpose eq64579 eq50390
    | exact resolve eq50390 eq64579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64579
  have eq66207 : x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq66165
       have r₂ := eq16
       grind)
    | exact resolve eq66165 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66165
  have eq66555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq386 y
       have i₂ := eq66207
       grind)
    | exact superpose eq66207 eq386
    | exact resolve eq386 eq66207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66207
  have eq66611 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq66555
       have r₂ := eq16
       grind)
    | exact resolve eq66555 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66555
  have eq66628 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65920
       have i₂ := eq66611
       grind)
    | exact superpose eq66611 eq65920
    | exact resolve eq65920 eq66611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65920
  have eq68067 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq66611
       grind)
    | exact superpose eq66611 eq10
    | exact resolve eq10 eq66611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66611
  have eq68188 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68067
       grind)
    | exact superpose eq68067 eq16
    | exact resolve eq16 eq68067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68924 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65524
       have i₂ := eq66628
       grind)
    | exact superpose eq66628 eq65524
    | exact resolve eq65524 eq66628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65524 eq66628
  have eq68943 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq68924
  have eq68944 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq68943
  have eq69165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50390 x
       have i₂ := eq68944
       grind)
    | exact superpose eq68944 eq50390
    | exact resolve eq50390 eq68944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50390 eq68944
  have eq69207 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq69165
       have i₂ := eq68067
       grind)
    | exact superpose eq68067 eq69165
    | exact resolve eq69165 eq68067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69165
  have eq69216 : x = (M.op y y) := by
    first
    | (have r₁ := eq69207
       have r₂ := eq68188
       grind)
    | exact resolve eq69207 eq68188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69207
  have eq69526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq386 y
       have i₂ := eq69216
       grind)
    | exact superpose eq69216 eq386
    | exact resolve eq386 eq69216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq69216
  have eq69582 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq69526
       have i₂ := eq68067
       grind)
    | exact superpose eq68067 eq69526
    | exact resolve eq69526 eq68067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68067 eq69526
  have eq69600 : False := by grind
  exact eq69600

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_pyx_pyy_pxy_pxy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0
    grind
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq20
    | (have j1 := eq37 (σ X0)
       grind)
    | exact resolve eq20 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq37 (τ X0)
       grind)
    | exact superpose eq37 eq23
    | (have j1 := eq37 (τ X0)
       grind)
    | exact resolve eq23 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41
    | (have j0 := eq41 X0
       grind)
    | exact resolve eq41 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | (have j0 := eq40 X0
       grind)
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X2) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 (τ (M.op (σ X0) (σ X0))))
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq43
    | (have j0 := eq43 X0
       have j1 := eq37 X0
       grind)
    | exact resolve eq43 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq55
    | (have j0 := eq55 X1 (σ X0)
       grind)
    | exact resolve eq55 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq110 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (σ (M.op (τ X0) (τ X0))))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq136 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq42
    | (have j0 := eq42 X0
       have j1 := eq37 X0
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq42
  have eq293 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq294 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq300 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq294 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq294 X1 X1
       have r₂ := eq53 X1 X1
       grind)
    | (have r₁ := eq294 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq53 X0 (M.op X1 X1)
       grind)
    | exact resolve eq294 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq294
  have eq317 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq300 X0 (τ X1)
       grind)
    | exact superpose eq300 eq23
    | (have j1 := eq300 X0 (τ X1)
       grind)
    | exact resolve eq23 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq94
    | (have j0 := eq94 X1 (σ X0)
       grind)
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq828 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq85
  have eq1028 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq317 X0 X1
       grind)
    | exact superpose eq317 eq10
    | (have j1 := eq317 X0 X1
       grind)
    | exact resolve eq10 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1082 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq136 (σ X0)
       grind)
    | exact superpose eq136 eq66
    | (have j1 := eq136 (σ X0)
       grind)
    | exact resolve eq66 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1085 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1082 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1082
    | (have j0 := eq1082 X0
       grind)
    | exact resolve eq1082 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1087 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1085 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1085
    | (have j0 := eq1085 X0
       grind)
    | exact resolve eq1085 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1089 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1087 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1087
    | (have j0 := eq1087 X0
       grind)
    | exact resolve eq1087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq2028 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq300 (σ X0) X1
       have i₂ := eq1028 X0 X1
       grind)
    | exact superpose eq1028 eq300
    | (have j0 := eq300 (σ X0) X1
       have j1 := eq1028 X0 X1
       grind)
    | exact resolve eq300 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq2031 : ∀ X0 X1 : G, (σ (k X1 (τ (σ X0)))) = (σ (M.op X0 (τ (σ X1)))) ∨ (M.op (τ (σ X1)) (τ (σ X1))) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq1028 X0 (σ X1)
       grind)
    | exact superpose eq1028 eq20
    | (have j1 := eq1028 X0 (σ X1)
       grind)
    | exact resolve eq20 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq2040 : ∀ X0 X1 : G, (σ (k X1 (τ (σ X0)))) = (σ (M.op X0 X1)) ∨ (M.op (τ (σ X1)) (τ (σ X1))) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2031 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq2031
    | (have j0 := eq2031 X0 X1
       grind)
    | exact resolve eq2031 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2065 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (τ (σ X1)) (τ (σ X1))) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2040 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2040
    | (have j0 := eq2040 X0 X1
       grind)
    | exact resolve eq2040 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2087 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2065 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2065
    | (have j0 := eq2065 X0 X1
       grind)
    | exact resolve eq2065 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2112 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2087 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq2087
    | (have j0 := eq2087 X0 X1
       grind)
    | exact resolve eq2087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2680 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq364 X0 X0
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq364
    | (have j0 := eq364 X0 X0
       have j1 := eq828 X0
       grind)
    | exact resolve eq364 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq828
  have eq2692 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680
  have eq2753 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0) (σ X0)
       have i₂ := eq2692 X0
       grind)
    | exact superpose eq2692 eq57
    | (have j0 := eq57 (σ X0) (σ X0)
       have j1 := eq2692 X0
       grind)
    | exact resolve eq57 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2757 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2761 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq2771 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2761 X0
       have j1 := eq2757 X0
       grind)
    | (have r₁ := eq2761 X0
       have r₂ := eq2757 X0
       grind)
    | exact resolve eq2761 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757 eq2761
  have eq2790 : ∀ X0 : G, (σ (k X0 (τ (σ X0)))) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2771 X0
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq2771
    | (have j0 := eq2771 X0
       grind)
    | exact resolve eq2771 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2807 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2790 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2790
    | (have j0 := eq2790 X0
       grind)
    | exact resolve eq2790 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq3460 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2807 (τ X0)
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq2807
    | (have j0 := eq2807 (τ X0)
       grind)
    | exact resolve eq2807 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2807
  have eq3506 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3460 X0
       have i₂ := eq10 (k X0 (σ (τ X0)))
       grind)
    | exact superpose eq10 eq3460
    | (have j0 := eq3460 X0
       grind)
    | exact resolve eq3460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460
  have eq3514 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3506 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3506
    | (have j0 := eq3506 X0
       grind)
    | exact resolve eq3506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq3518 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3514 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3514
    | (have j0 := eq3514 X0
       grind)
    | exact resolve eq3514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq3935 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    grind
  have eq3940 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq3518 (σ X0)
       grind)
    | exact superpose eq3518 eq66
    | (have j1 := eq3518 (σ X0)
       grind)
    | exact resolve eq66 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq3518
  have eq3950 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq3940 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3940
    | (have j0 := eq3940 X0
       grind)
    | exact resolve eq3940 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq3956 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3950 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3950
    | (have j0 := eq3950 X0
       grind)
    | exact resolve eq3950 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3950
  have eq3961 : ∀ X0 : G, (σ (k X0 (τ (σ X0)))) = (σ (M.op X0 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3956 X0
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq3956
    | (have j0 := eq3956 X0
       grind)
    | exact resolve eq3956 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq3963 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3961 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3961
    | (have j0 := eq3961 X0
       grind)
    | exact resolve eq3961 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961
  have eq4450 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3935 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq6661 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq3963 X0
       grind)
    | exact superpose eq3963 eq9
    | (have j1 := eq3963 X0
       grind)
    | exact resolve eq9 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq6689 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6661 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq6661
    | (have j0 := eq6661 X0
       grind)
    | exact resolve eq6661 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6661
  have eq6834 : ∀ X0 : G, (M.op X0 X0) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq6838 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1089 X0
       have j1 := eq6834 X0
       grind)
    | (have r₁ := eq1089 X0
       have r₂ := eq6834 X0
       grind)
    | exact resolve eq1089 eq6834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq6834
  have eq7057 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2112 X0 X0
       have i₂ := eq6838 X0
       grind)
    | exact superpose eq6838 eq2112
    | (have j0 := eq2112 X0 X0
       have j1 := eq6838 X0
       grind)
    | exact resolve eq2112 eq6838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq6838
  have eq7073 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057
  have eq7104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7073 X0
       have i₂ := eq10 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq10 eq7073
    | (have j0 := eq7073 X0
       grind)
    | exact resolve eq7073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7073
  have eq7389 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq7104 (τ X0)
       grind)
    | exact superpose eq7104 eq110
    | (have j1 := eq7104 (τ X0)
       grind)
    | exact resolve eq110 eq7104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7104
  have eq7405 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7389 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7389
    | (have j0 := eq7389 X0
       grind)
    | exact resolve eq7389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7389
  have eq7416 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7405 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7405
    | (have j0 := eq7405 X0
       grind)
    | exact resolve eq7405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7405
  have eq7419 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7416 X0
       have j1 := eq4450 X0
       grind)
    | (have r₁ := eq7416 X0
       have r₂ := eq4450 X0
       grind)
    | exact resolve eq7416 eq4450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450 eq7416
  have eq10615 : ∀ X0 : G, (σ (k X0 (τ (σ X0)))) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq7419 (σ X0)
       grind)
    | exact superpose eq7419 eq20
    | exact resolve eq20 eq7419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10627 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10615 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq10615
    | exact resolve eq10615 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq10643 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq10627 X0
       have i₂ := eq7419 X0
       grind)
    | exact superpose eq7419 eq10627
    | exact resolve eq10627 eq7419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10627
  have eq11181 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq10643 X0
       grind)
    | exact superpose eq10643 eq9
    | exact resolve eq9 eq10643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10643
  have eq11203 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11181 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq11181
    | exact resolve eq11181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11264 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq11203 X0
       grind)
    | exact superpose eq11203 eq110
    | exact resolve eq110 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq11277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7419 X0
       have i₂ := eq11203 X0
       grind)
    | exact superpose eq11203 eq7419
    | exact resolve eq7419 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419 eq11203
  have eq11659 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq11264
  have eq11785 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11659 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11659
    | exact resolve eq11659 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11659
  have eq11991 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq11277 (σ X0)
       grind)
    | exact superpose eq11277 eq20
    | exact resolve eq20 eq11277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11992 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq11277 (τ X0)
       grind)
    | exact superpose eq11277 eq23
    | exact resolve eq23 eq11277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11996 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11992 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11992
    | exact resolve eq11992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992
  have eq11997 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11991 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11991
    | exact resolve eq11991 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11991
  have eq12012 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11996 X0
       have i₂ := eq11277 X0
       grind)
    | exact superpose eq11277 eq11996
    | exact resolve eq11996 eq11277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11996
  have eq12013 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11997 X0
       have i₂ := eq11277 X0
       grind)
    | exact superpose eq11277 eq11997
    | exact resolve eq11997 eq11277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11277 eq11997
  have eq12070 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2028 X0 X1
       have i₂ := eq12012 X1
       grind)
    | exact superpose eq12012 eq2028
    | (have j0 := eq2028 X0 X1
       grind)
    | exact resolve eq2028 eq12012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq12991 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11785 X0
       have i₂ := eq12013 X0
       grind)
    | exact superpose eq12013 eq11785
    | exact resolve eq11785 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11785
  have eq13836 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12070 X0 X1
       have i₂ := eq12013 X0
       grind)
    | exact superpose eq12013 eq12070
    | (have j0 := eq12070 X0 X1
       grind)
    | exact resolve eq12070 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12070
  have eq17826 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq17851 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17826 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq17826
    | (have j0 := eq17826 X0
       grind)
    | exact resolve eq17826 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17826
  have eq17859 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17851 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17851
    | (have j0 := eq17851 X0
       grind)
    | exact resolve eq17851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17851
  have eq17865 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17859 X0
       have i₂ := eq12012 (M.op X0 X0)
       grind)
    | exact superpose eq12012 eq17859
    | (have j0 := eq17859 X0
       grind)
    | exact resolve eq17859 eq12012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12012 eq17859
  have eq17919 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq17942 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17919 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq17919
    | (have j0 := eq17919 X0
       grind)
    | exact resolve eq17919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17919
  have eq17949 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17942 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq17942
    | (have j0 := eq17942 X0
       grind)
    | exact resolve eq17942 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17942
  have eq17954 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq17949 X0
       have i₂ := eq12013 (M.op X0 X0)
       grind)
    | exact superpose eq12013 eq17949
    | (have j0 := eq17949 X0
       grind)
    | exact resolve eq17949 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17949
  have eq21784 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq17865 X0
       grind)
    | exact superpose eq17865 eq10
    | (have j1 := eq17865 X0
       grind)
    | exact resolve eq10 eq17865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17865
  have eq21806 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21784 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21784
    | (have j0 := eq21784 X0
       grind)
    | exact resolve eq21784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21784
  have eq22079 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21806 (σ X0)
       have i₂ := eq12013 X0
       grind)
    | exact superpose eq12013 eq21806
    | exact resolve eq21806 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22123 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22079 X0
       have i₂ := eq12013 (M.op X0 X0)
       grind)
    | exact superpose eq12013 eq22079
    | (have j0 := eq22079 X0
       grind)
    | exact resolve eq22079 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22079
  have eq22130 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22123 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq22123
    | (have j0 := eq22123 X0
       grind)
    | exact resolve eq22123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22123
  have eq22135 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22130 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq22130
    | (have j0 := eq22130 X0
       grind)
    | exact resolve eq22130 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22130
  have eq22139 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (σ (k (M.op X0 X0) (τ (σ X0))))) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22135 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq22135
    | (have j0 := eq22135 X0
       grind)
    | exact resolve eq22135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22135
  have eq22141 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (τ (σ X0))) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22139 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq22139
    | (have j0 := eq22139 X0
       grind)
    | exact resolve eq22139 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22139
  have eq22143 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq22141 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq22141
    | (have j0 := eq22141 X0
       grind)
    | exact resolve eq22141 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22141
  have eq22550 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq17954 X0
       grind)
    | exact superpose eq17954 eq9
    | (have j1 := eq17954 X0
       grind)
    | exact resolve eq9 eq17954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22578 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq22550 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq22550
    | (have j0 := eq22550 X0
       grind)
    | exact resolve eq22550 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22550
  have eq33325 : (σ (M.op x y)) ≠ (σ (M.op x (τ (σ y)))) ∨ x = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13836 x (σ y)
       grind)
    | exact superpose eq13836 eq16
    | (have j1 := eq13836 x (σ y)
       grind)
    | exact resolve eq16 eq13836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13836
  have eq33450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq33325
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33325
    | exact resolve eq33325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33325
  have eq33451 : x = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (τ (σ y)) := by grind
  clear eq33450
  have eq33507 : x = (τ (σ (M.op y y))) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq33451
       have i₂ := eq12013 y
       grind)
    | exact superpose eq12013 eq33451
    | exact resolve eq33451 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33451
  have eq33546 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq33507
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq33507
    | exact resolve eq33507 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33507
  have eq33572 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq33546
       have i₂ := eq12013 y
       grind)
    | exact superpose eq12013 eq33546
    | exact resolve eq33546 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12013 eq33546
  have eq33591 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq33572
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33572
    | exact resolve eq33572 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33572
  have eq33637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12991 x
       have i₂ := eq33591
       grind)
    | exact superpose eq33591 eq12991
    | exact resolve eq12991 eq33591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33591
  have eq33692 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq33637
       have r₂ := eq16
       grind)
    | exact resolve eq33637 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33637
  have eq34025 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17954 y
       have i₂ := eq33692
       grind)
    | exact superpose eq33692 eq17954
    | exact resolve eq17954 eq33692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17954
  have eq34036 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22143 y
       have i₂ := eq33692
       grind)
    | exact superpose eq33692 eq22143
    | exact resolve eq22143 eq33692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22143 eq33692
  have eq34060 : (M.op x y) = (k x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34036
  have eq34061 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34025
  have eq36217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq34061
       have i₂ := eq34060
       grind)
    | exact superpose eq34060 eq34061
    | exact resolve eq34061 eq34060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34060 eq34061
  have eq36281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq36217
  have eq36283 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq36281
       have r₂ := eq16
       grind)
    | exact resolve eq36281 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36281
  have eq36432 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq36283
       grind)
    | exact superpose eq36283 eq9
    | exact resolve eq9 eq36283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36283
  have eq36482 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq36432
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq36432
    | exact resolve eq36432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36432
  have eq36663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12991 x
       have i₂ := eq36482
       grind)
    | exact superpose eq36482 eq12991
    | exact resolve eq12991 eq36482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36482
  have eq36723 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq36663
       have r₂ := eq16
       grind)
    | exact resolve eq36663 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36663
  have eq36917 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq36723
       grind)
    | exact superpose eq36723 eq9
    | exact resolve eq9 eq36723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36723
  have eq36973 : x = (M.op y y) := by
    first
    | (have i₁ := eq36917
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq36917
    | exact resolve eq36917 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36917
  have eq37856 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by grind
  have eq37881 : y = (M.op x x) ∨ (M.op (τ x) (τ y)) = (τ (k x y)) := by
    first
    | (have i₁ := eq21806 y
       have i₂ := eq36973
       grind)
    | exact superpose eq36973 eq21806
    | exact resolve eq21806 eq36973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21806
  have eq37884 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq22578 y
       have i₂ := eq36973
       grind)
    | exact superpose eq36973 eq22578
    | exact resolve eq22578 eq36973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22578 eq36973
  have eq41005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (τ x) (τ y)) = (τ (k x y)) := by
    first
    | (have i₁ := eq12991 x
       have i₂ := eq37881
       grind)
    | exact superpose eq37881 eq12991
    | exact resolve eq12991 eq37881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37881
  have eq41068 : (M.op (τ x) (τ y)) = (τ (k x y)) := by
    first
    | (have r₁ := eq41005
       have r₂ := eq16
       grind)
    | exact resolve eq41005 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41005
  have eq41573 : (k x y) = (σ (M.op (τ x) (τ y))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq41068
       grind)
    | exact superpose eq41068 eq10
    | exact resolve eq10 eq41068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41068
  have eq41652 : y = (M.op x x) ∨ (M.op x y) = (σ (M.op (τ x) (τ y))) := by
    first
    | (have i₁ := eq37856
       have i₂ := eq41573
       grind)
    | exact superpose eq41573 eq37856
    | exact resolve eq37856 eq41573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37856
  have eq41655 : (M.op (σ x) (σ y)) = (σ (σ (M.op (τ x) (τ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq37884
       have i₂ := eq41573
       grind)
    | exact superpose eq41573 eq37884
    | exact resolve eq37884 eq41573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37884 eq41573
  have eq42992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op (τ x) (τ y))) := by
    first
    | (have i₁ := eq12991 x
       have i₂ := eq41652
       grind)
    | exact superpose eq41652 eq12991
    | exact resolve eq12991 eq41652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41652
  have eq43057 : (M.op x y) = (σ (M.op (τ x) (τ y))) := by
    first
    | (have r₁ := eq42992
       have r₂ := eq16
       grind)
    | exact resolve eq42992 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42992
  have eq43069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41655
       have i₂ := eq43057
       grind)
    | exact superpose eq43057 eq41655
    | exact resolve eq41655 eq43057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41655 eq43057
  have eq43072 : y = (M.op x x) := by
    first
    | (have r₁ := eq43069
       have r₂ := eq16
       grind)
    | exact resolve eq43069 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43069
  have eq43253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12991 x
       have i₂ := eq43072
       grind)
    | exact superpose eq43072 eq12991
    | exact resolve eq12991 eq43072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12991 eq43072
  have eq43317 : False := by grind
  exact eq43317

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_pyx_x_pxy_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    grind
  have eq41 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 (τ (M.op (σ X0) (σ X0))))
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq56 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq61 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq20 (σ x) y
       grind)
    | exact superpose eq20 eq56
    | exact resolve eq56 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq71 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq20
    | (have j1 := eq63 (σ X0)
       grind)
    | exact resolve eq20 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq23
    | (have j1 := eq63 (τ X0)
       grind)
    | exact resolve eq23 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X0
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X1) X0
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq67
    | (have j0 := eq67 (σ X0) X1
       grind)
    | exact resolve eq67 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq67
    | (have j0 := eq67 (τ X0) X1
       grind)
    | exact resolve eq67 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq92 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq98 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq98
  have eq124 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 X1 (σ X0)
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq170 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq76
  have eq171 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq170 X0
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq170
    | (have j0 := eq170 X0
       grind)
    | exact resolve eq170 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq173 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq171 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq171
    | (have j0 := eq171 X0
       grind)
    | exact resolve eq171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq174 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq180 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq41
    | (have j1 := eq92 X0
       grind)
    | exact resolve eq41 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq92
  have eq184 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq180
    | (have j0 := eq180 X0
       grind)
    | exact resolve eq180 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq185 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq188 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq63
    | (have j0 := eq63 X0
       grind)
    | exact resolve eq63 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq194 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq174
    | exact resolve eq174 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq199 : ∀ X0 X1 : G, (τ (τ (M.op (σ X0) (σ X0)))) = X1 ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq248 : ∀ X0 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq185 (τ X0)
       grind)
    | exact superpose eq185 eq23
    | exact resolve eq23 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq248 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248
    | exact resolve eq248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq256 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq251
    | exact resolve eq251 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq256 X0
       grind)
    | exact superpose eq256 eq194
    | exact resolve eq194 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq262 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq256 X0
       grind)
    | exact superpose eq256 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq256
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    grind
  clear eq188
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq281 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq279 X0
       grind)
    | exact superpose eq279 eq185
    | exact resolve eq185 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq279
  have eq289 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq281 (σ X0)
       grind)
    | exact superpose eq281 eq20
    | exact resolve eq20 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq289
    | exact resolve eq289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq297 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq292
    | exact resolve eq292 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq292
  have eq303 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq314 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq297 x
       grind)
    | exact superpose eq297 eq99
    | exact resolve eq99 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq315 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq297 x
       grind)
    | exact superpose eq297 eq71
    | exact resolve eq71 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq316 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq315
       have i₂ := eq297 y
       grind)
    | exact superpose eq297 eq315
    | exact resolve eq315 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq317 : (M.op x y) = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq314
       have i₂ := eq297 y
       grind)
    | exact superpose eq297 eq314
    | exact resolve eq314 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq320 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq297 X1
       grind)
    | exact superpose eq297 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq325 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq326 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq333 : ∀ X0 : G, (τ (k X0 (σ (τ (M.op X0 X0))))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq23 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq23 eq326
    | exact resolve eq326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq334 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq325
    | (have j0 := eq325 X0
       grind)
    | exact resolve eq325 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq336 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq333
    | exact resolve eq333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq337 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq334
    | (have j0 := eq334 X0
       grind)
    | exact resolve eq334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq338 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq336
  have eq339 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq261 (M.op X0 X0)
       grind)
    | exact superpose eq261 eq337
    | (have j0 := eq337 X0
       grind)
    | exact resolve eq337 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq373 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq374 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq381 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq20 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq20 eq374
    | exact resolve eq374 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq382 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq373
    | (have j0 := eq373 X0
       grind)
    | exact resolve eq373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq384 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq381
    | exact resolve eq381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq385 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq382 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq382
    | (have j0 := eq382 X0
       grind)
    | exact resolve eq382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq386 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq384
  have eq387 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq297 (M.op X0 X0)
       grind)
    | exact superpose eq297 eq385
    | (have j0 := eq385 X0
       grind)
    | exact resolve eq385 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq445 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (τ (k X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq262 X1 X0
       grind)
    | exact superpose eq262 eq10
    | (have j1 := eq262 X1 X0
       grind)
    | exact resolve eq10 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq320 x y
       have i₂ := eq317
       grind)
    | exact superpose eq317 eq320
    | (have j0 := eq320 x y
       grind)
    | exact resolve eq320 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq320
  have eq607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq596
  have eq611 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq607
       have r₂ := eq16
       grind)
    | exact resolve eq607 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq615 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq611
       have r₂ := eq316
       grind)
    | exact resolve eq611 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq611
  have eq1040 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq10
    | (have j1 := eq339 X0
       grind)
    | exact resolve eq10 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq1056 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1040 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1040
    | (have j0 := eq1040 X0
       grind)
    | exact resolve eq1040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1095 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq338 (M.op X0 X0)
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq338
    | (have j1 := eq1056 X0
       grind)
    | exact resolve eq338 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq1056
  have eq1280 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq9
    | (have j1 := eq387 X0
       grind)
    | exact resolve eq9 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq1297 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1280 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1280
    | (have j0 := eq1280 X0
       grind)
    | exact resolve eq1280 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1319 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 (σ X1)
       have i₂ := eq20 (σ X0) X1
       grind)
    | exact superpose eq20 eq445
    | (have j0 := eq445 X1 (σ X0)
       grind)
    | exact resolve eq445 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq1343 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1319 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1319
    | (have j0 := eq1319 X0 X1
       grind)
    | exact resolve eq1319 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1354 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1343 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1343
    | (have j0 := eq1343 X0 X1
       grind)
    | exact resolve eq1343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1358 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq1354
    | (have j0 := eq1354 X0 X1
       grind)
    | exact resolve eq1354 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1362 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1358 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq1358
    | (have j0 := eq1358 X0 X1
       grind)
    | exact resolve eq1358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1366 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1362 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1362
    | (have j0 := eq1362 X0 X1
       grind)
    | exact resolve eq1362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1370 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1366 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq1366
    | (have j0 := eq1366 X0 X1
       grind)
    | exact resolve eq1366 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq1373 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1370 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1370
    | (have j0 := eq1370 X0 X1
       grind)
    | exact resolve eq1370 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1373 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1373
    | (have j0 := eq1373 X0 X1
       grind)
    | exact resolve eq1373 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1385 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq386 (M.op X0 X0)
       have i₂ := eq1297 X0
       grind)
    | exact superpose eq1297 eq386
    | (have j1 := eq1297 X0
       grind)
    | exact resolve eq386 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1847 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq615
       grind)
    | exact superpose eq615 eq9
    | exact resolve eq9 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq1864 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1847
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1847
    | exact resolve eq1847 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq1865 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by grind
  clear eq1864
  have eq3637 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1095 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1095
    | exact resolve eq1095 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq3654 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3637 X0
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq3637
    | (have j0 := eq3637 X0
       grind)
    | exact resolve eq3637 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3660 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3654 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3654
    | (have j0 := eq3654 X0
       grind)
    | exact resolve eq3654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654
  have eq3666 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3660 X0
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq3660
    | (have j0 := eq3660 X0
       grind)
    | exact resolve eq3660 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660
  have eq3670 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3666 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3666
    | (have j0 := eq3666 X0
       grind)
    | exact resolve eq3666 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3672 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (σ (k (M.op X0 X0) (τ (σ X0))))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3670 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq3670
    | (have j0 := eq3670 X0
       grind)
    | exact resolve eq3670 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3674 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (τ (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3672 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq3672
    | (have j0 := eq3672 X0
       grind)
    | exact resolve eq3672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq3676 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3674 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3674
    | (have j0 := eq3674 X0
       grind)
    | exact resolve eq3674 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674
  have eq6280 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1385 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1385
    | exact resolve eq1385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq6307 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (σ (τ (M.op X0 X0))) X0) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6280 X0
       have i₂ := eq261 X0
       grind)
    | exact superpose eq261 eq6280
    | (have j0 := eq6280 X0
       grind)
    | exact resolve eq6280 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6280
  have eq6322 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6307 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6307
    | (have j0 := eq6307 X0
       grind)
    | exact resolve eq6307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6337 : ∀ X0 : G, (σ (k (τ (M.op X0 X0)) (τ X0))) = (M.op (σ (τ (M.op X0 X0))) X0) ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6322 X0
       have i₂ := eq261 X0
       grind)
    | exact superpose eq261 eq6322
    | (have j0 := eq6322 X0
       grind)
    | exact resolve eq6322 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq6322
  have eq6348 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (k (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6337 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6337
    | (have j0 := eq6337 X0
       grind)
    | exact resolve eq6337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6337
  have eq6359 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (τ (k (M.op X0 X0) (σ (τ X0))))) ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6348 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq6348
    | (have j0 := eq6348 X0
       grind)
    | exact resolve eq6348 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6348
  have eq6363 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (σ (τ X0))) ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6359 X0
       have i₂ := eq10 (k (M.op X0 X0) (σ (τ X0)))
       grind)
    | exact superpose eq10 eq6359
    | (have j0 := eq6359 X0
       grind)
    | exact resolve eq6359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq6367 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq6363 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6363
    | (have j0 := eq6363 X0
       grind)
    | exact resolve eq6363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6363
  have eq6547 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ (M.op X0 X0)) (τ X0))
       have i₂ := eq6367 X0
       grind)
    | exact superpose eq6367 eq9
    | (have j1 := eq6367 X0
       grind)
    | exact resolve eq9 eq6367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367
  have eq6796 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) (τ (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6547 (σ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq6547
    | exact resolve eq6547 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq6547
  have eq6837 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6796 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6796
    | (have j0 := eq6796 X0
       grind)
    | exact resolve eq6796 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6796
  have eq6842 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6837 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq6837
    | (have j0 := eq6837 X0
       grind)
    | exact resolve eq6837 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6837
  have eq6846 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) (τ (σ X0)))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6842 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq6842
    | (have j0 := eq6842 X0
       grind)
    | exact resolve eq6842 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6842
  have eq6850 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6846 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6846
    | (have j0 := eq6846 X0
       grind)
    | exact resolve eq6846 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6846
  have eq9963 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0)
       have i₂ := eq6850 X0
       grind)
    | exact superpose eq6850 eq9
    | (have j1 := eq6850 X0
       grind)
    | exact resolve eq9 eq6850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6850
  have eq11377 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3676 X0
       have i₂ := eq9963 X0
       grind)
    | exact superpose eq9963 eq3676
    | (have j0 := eq3676 X0
       have j1 := eq9963 X0
       grind)
    | exact resolve eq3676 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676 eq9963
  have eq11417 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq11377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11377
  have eq11802 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ (M.op X0 X0)) (σ X0))
       have i₂ := eq11417 X0
       grind)
    | exact superpose eq11417 eq10
    | exact resolve eq10 eq11417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11417
  have eq13083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11802 y
       have i₂ := eq1865
       grind)
    | exact superpose eq1865 eq11802
    | exact resolve eq11802 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq13145 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq13083
       have r₂ := eq16
       grind)
    | exact resolve eq13083 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13083
  have eq15036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq386 x
       have i₂ := eq13145
       grind)
    | exact superpose eq13145 eq386
    | exact resolve eq386 eq13145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13145
  have eq15068 : (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq15036
       have r₂ := eq16
       grind)
    | exact resolve eq15036 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15036
  have eq15259 : (τ (σ x)) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq15068
       grind)
    | exact superpose eq15068 eq9
    | exact resolve eq9 eq15068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15068
  have eq15298 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq15259
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq15259
    | exact resolve eq15259 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15259
  have eq15387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11802 y
       have i₂ := eq15298
       grind)
    | exact superpose eq15298 eq11802
    | exact resolve eq11802 eq15298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq15405 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq15387
       have r₂ := eq16
       grind)
    | exact resolve eq15387 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15387
  have eq15468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1376 y x
       have i₂ := eq15405
       grind)
    | exact superpose eq15405 eq1376
    | (have j0 := eq1376 y x
       grind)
    | exact resolve eq1376 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq15469 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq15405
       grind)
    | exact superpose eq15405 eq9
    | exact resolve eq9 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405
  have eq15540 : y = (M.op x x) ∨ x = (M.op y y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq15468
       have r₂ := eq16
       grind)
    | exact resolve eq15468 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq15582 : y = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15540
       have i₂ := eq15469
       grind)
    | exact superpose eq15469 eq15540
    | exact resolve eq15540 eq15469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15540
  have eq16077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq386 x
       have i₂ := eq15582
       grind)
    | exact superpose eq15582 eq386
    | exact resolve eq386 eq15582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15582
  have eq16119 : x = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq16077
       have r₂ := eq16
       grind)
    | exact resolve eq16077 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077
  have eq16278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11802 y
       have i₂ := eq16119
       grind)
    | exact superpose eq16119 eq11802
    | exact resolve eq11802 eq16119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16119
  have eq16296 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq16278
       have r₂ := eq16
       grind)
    | exact resolve eq16278 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278
  have eq16299 : y = (k y x) := by
    first
    | (have i₁ := eq15469
       have i₂ := eq16296
       grind)
    | exact superpose eq16296 eq15469
    | exact resolve eq15469 eq16296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15469
  have eq16992 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq16296
       grind)
    | exact superpose eq16296 eq10
    | exact resolve eq10 eq16296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16296
  have eq17065 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16992
       grind)
    | exact superpose eq16992 eq16
    | exact resolve eq16 eq16992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17277 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17065
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq17065
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq17065 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17280 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq17277
  have eq17281 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17280
       have i₂ := eq16299
       grind)
    | exact superpose eq16299 eq17280
    | exact resolve eq17280 eq16299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299 eq17280
  have eq17310 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17065
       have i₂ := eq17281
       grind)
    | exact superpose eq17281 eq17065
    | exact resolve eq17065 eq17281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281
  have eq17314 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq17310
  have eq17320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq386 x
       have i₂ := eq17314
       grind)
    | exact superpose eq17314 eq386
    | exact resolve eq386 eq17314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq17314
  have eq17362 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17320
       have i₂ := eq16992
       grind)
    | exact superpose eq16992 eq17320
    | exact resolve eq17320 eq16992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17320
  have eq17365 : x = (M.op y y) := by
    first
    | (have r₁ := eq17362
       have r₂ := eq17065
       grind)
    | exact resolve eq17362 eq17065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17362
  have eq17682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11802 y
       have i₂ := eq17365
       grind)
    | exact superpose eq17365 eq11802
    | exact resolve eq11802 eq17365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11802 eq17365
  have eq17700 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq17682
       have i₂ := eq16992
       grind)
    | exact superpose eq16992 eq17682
    | exact resolve eq17682 eq16992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16992 eq17682
  have eq17702 : False := by grind
  exact eq17702

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_pyx_y_pxy_pxy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    grind
  have eq41 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 (τ (M.op (σ X0) (σ X0))))
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq56 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq61 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq20 (σ x) y
       grind)
    | exact superpose eq20 eq56
    | exact resolve eq56 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq71 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq20
    | (have j1 := eq63 (σ X0)
       grind)
    | exact resolve eq20 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq23
    | (have j1 := eq63 (τ X0)
       grind)
    | exact resolve eq23 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X0
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq67
    | (have j0 := eq67 X1 (σ X0)
       grind)
    | exact resolve eq67 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (τ X0)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq67
    | (have j0 := eq67 X1 (τ X0)
       grind)
    | exact resolve eq67 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | (have j1 := eq77 X0
       grind)
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq98 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq98
  have eq124 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 X1 (σ X0)
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq168 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq76
  have eq169 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq168 X0
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq168
    | (have j0 := eq168 X0
       grind)
    | exact resolve eq168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq171 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq169 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169
    | (have j0 := eq169 X0
       grind)
    | exact resolve eq169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq172 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq178 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq41
    | (have j1 := eq92 X0
       grind)
    | exact resolve eq41 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq92
  have eq182 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq178
    | (have j0 := eq178 X0
       grind)
    | exact resolve eq178 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq183 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq186 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq63
    | (have j0 := eq63 X0
       grind)
    | exact resolve eq63 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq192 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq172 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq172
    | exact resolve eq172 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq197 : ∀ X0 X1 : G, (τ (τ (M.op (σ X0) (σ X0)))) = X1 ∨ (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq244 : ∀ X0 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq183 (τ X0)
       grind)
    | exact superpose eq183 eq23
    | exact resolve eq23 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq244 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq244
    | exact resolve eq244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq252 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq247 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq247
    | exact resolve eq247 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq257 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq192 X0
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq192
    | exact resolve eq192 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq258 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq197
    | (have j0 := eq197 X0 X1
       grind)
    | exact resolve eq197 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq252
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    grind
  clear eq186
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq272
    | (have j0 := eq272 X0
       grind)
    | exact resolve eq272 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq275 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq274 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq183
    | exact resolve eq183 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq275
  have eq285 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq277 (σ X0)
       grind)
    | exact superpose eq277 eq20
    | exact resolve eq20 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq285
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq293 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq288
    | exact resolve eq288 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq288
  have eq299 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq310 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq293 x
       grind)
    | exact superpose eq293 eq99
    | exact resolve eq99 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq311 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq293 x
       grind)
    | exact superpose eq293 eq71
    | exact resolve eq71 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq312 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq311
       have i₂ := eq293 y
       grind)
    | exact superpose eq293 eq311
    | exact resolve eq311 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq313 : (M.op x y) = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq310
       have i₂ := eq293 y
       grind)
    | exact superpose eq293 eq310
    | exact resolve eq310 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq293 X1
       grind)
    | exact superpose eq293 eq299
    | (have j0 := eq299 X0 X1
       grind)
    | exact resolve eq299 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq321 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq322 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq329 : ∀ X0 : G, (τ (k X0 (σ (τ (M.op X0 X0))))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq322 X0
       have i₂ := eq23 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq23 eq322
    | exact resolve eq322 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq330 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq23 (M.op X0 X0) (τ X0)
       grind)
    | exact superpose eq23 eq321
    | (have j0 := eq321 X0
       grind)
    | exact resolve eq321 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq321
  have eq332 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq329 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq329
    | exact resolve eq329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq333 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq330 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330
    | (have j0 := eq330 X0
       grind)
    | exact resolve eq330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq334 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq332
  have eq335 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq257 (M.op X0 X0)
       grind)
    | exact superpose eq257 eq333
    | (have j0 := eq333 X0
       grind)
    | exact resolve eq333 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq333
  have eq369 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq370 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq377 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq20 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq20 eq370
    | exact resolve eq370 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq378 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq369 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq369
    | (have j0 := eq369 X0
       grind)
    | exact resolve eq369 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq380 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq377 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq377
    | exact resolve eq377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq381 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq378
    | (have j0 := eq378 X0
       grind)
    | exact resolve eq378 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq382 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq380
  have eq383 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq293 (M.op X0 X0)
       grind)
    | exact superpose eq293 eq381
    | (have j0 := eq381 X0
       grind)
    | exact resolve eq381 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq441 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (τ X1) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq258 X1 X0
       grind)
    | exact superpose eq258 eq10
    | (have j1 := eq258 X1 X0
       grind)
    | exact resolve eq10 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq316 x y
       have i₂ := eq313
       grind)
    | exact superpose eq313 eq316
    | (have j0 := eq316 x y
       grind)
    | exact resolve eq316 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq316
  have eq602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq591
  have eq604 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq602
       have r₂ := eq16
       grind)
    | exact resolve eq602 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq608 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq604
       have r₂ := eq312
       grind)
    | exact resolve eq604 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq604
  have eq1103 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq335 X0
       grind)
    | exact superpose eq335 eq10
    | (have j1 := eq335 X0
       grind)
    | exact resolve eq10 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq1120 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1103 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1103
    | (have j0 := eq1103 X0
       grind)
    | exact resolve eq1103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1168 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq334 (M.op X0 X0)
       have i₂ := eq1120 X0
       grind)
    | exact superpose eq1120 eq334
    | (have j1 := eq1120 X0
       grind)
    | exact resolve eq334 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq1120
  have eq1200 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 (σ X1)
       have i₂ := eq20 (σ X0) X1
       grind)
    | exact superpose eq20 eq441
    | (have j0 := eq441 X1 (σ X0)
       grind)
    | exact resolve eq441 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq1225 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1225 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1225
    | (have j0 := eq1225 X0 X1
       grind)
    | exact resolve eq1225 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1240 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1236 X0 X1
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq1236
    | (have j0 := eq1236 X0 X1
       grind)
    | exact resolve eq1236 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1244 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (M.op X1 X1) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1240 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq1240
    | (have j0 := eq1240 X0 X1
       grind)
    | exact resolve eq1240 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1248 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1244
    | (have j0 := eq1244 X0 X1
       grind)
    | exact resolve eq1244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1252 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1248 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq1248
    | (have j0 := eq1248 X0 X1
       grind)
    | exact resolve eq1248 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1255 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1252 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1252
    | (have j0 := eq1252 X0 X1
       grind)
    | exact resolve eq1252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1393 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq383 X0
       grind)
    | exact superpose eq383 eq9
    | (have j1 := eq383 X0
       grind)
    | exact resolve eq9 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq1411 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1393 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1393
    | (have j0 := eq1393 X0
       grind)
    | exact resolve eq1393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1471 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq382 (M.op X0 X0)
       have i₂ := eq1411 X0
       grind)
    | exact superpose eq1411 eq382
    | (have j1 := eq1411 X0
       grind)
    | exact resolve eq382 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq608
       grind)
    | exact superpose eq608 eq382
    | exact resolve eq382 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq1805 : (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1782
       have r₂ := eq16
       grind)
    | exact resolve eq1782 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq3849 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1168 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1168
    | exact resolve eq1168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq3867 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3849 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq3849
    | (have j0 := eq3849 X0
       grind)
    | exact resolve eq3849 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3849
  have eq3874 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3867 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3867
    | (have j0 := eq3867 X0
       grind)
    | exact resolve eq3867 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867
  have eq3881 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3874 X0
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq3874
    | (have j0 := eq3874 X0
       grind)
    | exact resolve eq3874 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq3874
  have eq3885 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3881 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3881
    | (have j0 := eq3881 X0
       grind)
    | exact resolve eq3881 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3881
  have eq3887 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (σ (k (M.op X0 X0) (τ (σ X0))))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3885 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq3885
    | (have j0 := eq3885 X0
       grind)
    | exact resolve eq3885 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3885
  have eq3889 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (τ (σ X0))) ∨ (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3887 X0
       have i₂ := eq9 (k (M.op X0 X0) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq3887
    | (have j0 := eq3887 X0
       grind)
    | exact resolve eq3887 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3891 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3889 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3889
    | (have j0 := eq3889 X0
       grind)
    | exact resolve eq3889 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq17856 : (τ (σ x)) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1805
       grind)
    | exact superpose eq1805 eq9
    | exact resolve eq9 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq17905 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17856
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq17856
    | exact resolve eq17856 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17856
  have eq17906 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) := by grind
  clear eq17905
  have eq17973 : (M.op x x) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq17906
       grind)
    | exact superpose eq17906 eq9
    | exact resolve eq9 eq17906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17906
  have eq18022 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17973
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17973
    | exact resolve eq17973 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17973
  have eq18893 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by grind
  have eq18914 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1411 y
       have i₂ := eq18022
       grind)
    | exact superpose eq18022 eq1411
    | exact resolve eq1411 eq18022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18022
  have eq18957 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq18914
  have eq18959 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq18893
  have eq21596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq18957
       grind)
    | exact superpose eq18957 eq382
    | exact resolve eq382 eq18957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18957
  have eq21659 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq21596
       have r₂ := eq16
       grind)
    | exact resolve eq21596 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21596
  have eq21865 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq21659
       grind)
    | exact superpose eq21659 eq9
    | exact resolve eq9 eq21659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22186 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1255 y x
       have i₂ := eq21865
       grind)
    | exact superpose eq21865 eq1255
    | (have j0 := eq1255 y x
       grind)
    | exact resolve eq1255 eq21865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21865
  have eq22205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq22186
       have i₂ := eq10 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq10 eq22186
    | exact resolve eq22186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22186
  have eq22215 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq22205
       have r₂ := eq16
       grind)
    | exact resolve eq22205 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22205
  have eq42214 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1411 y
       have i₂ := eq22215
       grind)
    | exact superpose eq22215 eq1411
    | exact resolve eq1411 eq22215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22215
  have eq42273 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq42214
  have eq42535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq42273
       grind)
    | exact superpose eq42273 eq382
    | exact resolve eq382 eq42273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42273
  have eq42614 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq42535
       have r₂ := eq16
       grind)
    | exact resolve eq42535 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42535
  have eq43114 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq42614
       grind)
    | exact superpose eq42614 eq10
    | exact resolve eq10 eq42614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42614
  have eq43507 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43114
       grind)
    | exact superpose eq43114 eq16
    | exact resolve eq16 eq43114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43114
  have eq44228 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq43507
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq43507
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq43507 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43507
  have eq44235 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq44228
  have eq46647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21659
       have i₂ := eq44235
       grind)
    | exact superpose eq44235 eq21659
    | exact resolve eq21659 eq44235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21659 eq44235
  have eq46699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq46647
  have eq46724 : x = (M.op y y) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq46699
       have r₂ := eq16
       grind)
    | exact resolve eq46699 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46699
  have eq47026 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1411 y
       have i₂ := eq46724
       grind)
    | exact superpose eq46724 eq1411
    | exact resolve eq1411 eq46724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411 eq46724
  have eq47085 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq47026
  have eq47937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq47085
       grind)
    | exact superpose eq47085 eq382
    | exact resolve eq382 eq47085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47085
  have eq48016 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq47937
       have r₂ := eq16
       grind)
    | exact resolve eq47937 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47937
  have eq48572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq48016
       have i₂ := eq18959
       grind)
    | exact superpose eq18959 eq48016
    | exact resolve eq48016 eq18959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq48606 : (τ (M.op (σ x) (σ y))) = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq48016
       grind)
    | exact superpose eq48016 eq9
    | exact resolve eq9 eq48016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48016
  have eq49572 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq48572
       have r₂ := eq16
       grind)
    | exact resolve eq48572 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48572
  have eq52849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq49572
       grind)
    | exact superpose eq49572 eq382
    | exact resolve eq382 eq49572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49572
  have eq52929 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq52849
       have r₂ := eq16
       grind)
    | exact resolve eq52849 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52849
  have eq53241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq52929
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq52929
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq52929 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq53246 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq52929
       have i₂ := eq1255 y x
       grind)
    | exact superpose eq1255 eq52929
    | (have j1 := eq1255 y x
       grind)
    | exact resolve eq52929 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq53267 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq52929
       grind)
    | exact superpose eq52929 eq9
    | exact resolve eq9 eq52929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52929
  have eq53633 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53246
       have i₂ := eq53267
       grind)
    | exact superpose eq53267 eq53246
    | exact resolve eq53246 eq53267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53246
  have eq53637 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq53241
       have r₂ := eq16
       grind)
    | exact resolve eq53241 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53241
  have eq53870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53633
       have i₂ := eq10 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq10 eq53633
    | exact resolve eq53633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53633
  have eq53874 : y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53637
       have i₂ := eq53267
       grind)
    | exact superpose eq53267 eq53637
    | exact resolve eq53637 eq53267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53637
  have eq54066 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq53870
       have r₂ := eq16
       grind)
    | exact resolve eq53870 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53870
  have eq55278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq53874
       grind)
    | exact superpose eq53874 eq382
    | exact resolve eq382 eq53874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53874
  have eq55398 : x = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq55278
       have r₂ := eq16
       grind)
    | exact resolve eq55278 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55278
  have eq56658 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54066
       grind)
    | exact superpose eq54066 eq16
    | exact resolve eq16 eq54066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54066
  have eq57158 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56658
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq56658
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq56658 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57168 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
  clear eq57158
  have eq57169 : y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
  clear eq57168
  have eq57170 : y = (M.op x x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57169
       have i₂ := eq53267
       grind)
    | exact superpose eq53267 eq57169
    | exact resolve eq57169 eq53267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53267 eq57169
  have eq63080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq57170
       grind)
    | exact superpose eq57170 eq382
    | exact resolve eq382 eq57170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57170
  have eq63200 : x = (M.op y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq63080
       have r₂ := eq16
       grind)
    | exact resolve eq63080 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63080
  have eq63441 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3891 y
       have i₂ := eq63200
       grind)
    | exact superpose eq63200 eq3891
    | exact resolve eq3891 eq63200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891 eq63200
  have eq63484 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by grind
  clear eq63441
  have eq63518 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq63484
       have i₂ := eq48606
       grind)
    | exact superpose eq48606 eq63484
    | exact resolve eq63484 eq48606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63484
  have eq63519 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq63518
  have eq63595 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq48606
       have i₂ := eq63519
       grind)
    | exact superpose eq63519 eq48606
    | exact resolve eq48606 eq63519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48606
  have eq63734 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55398
       have i₂ := eq63519
       grind)
    | exact superpose eq63519 eq55398
    | exact resolve eq55398 eq63519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55398 eq63519
  have eq64696 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56658
       have i₂ := eq63734
       grind)
    | exact superpose eq63734 eq56658
    | exact resolve eq56658 eq63734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56658 eq63734
  have eq64712 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq64696
  have eq64713 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq64712
  have eq64898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq382 x
       have i₂ := eq64713
       grind)
    | exact superpose eq64713 eq382
    | exact resolve eq382 eq64713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq64713
  have eq65018 : x = (M.op y y) := by
    first
    | (have r₁ := eq64898
       have r₂ := eq16
       grind)
    | exact resolve eq64898 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64898
  have eq65117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1471 y
       have i₂ := eq65018
       grind)
    | exact superpose eq65018 eq1471
    | exact resolve eq1471 eq65018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq65018
  have eq65189 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq65117
       have r₂ := eq16
       grind)
    | exact resolve eq65117 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65117
  have eq65210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65189
       have i₂ := eq63595
       grind)
    | exact superpose eq63595 eq65189
    | exact resolve eq65189 eq63595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63595 eq65189
  have eq65231 : False := by grind
  exact eq65231

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_x_y_pxy_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : (M.op x y) = (M.op x y) := by grind
  have eq21 : (M.op x y) = (M.op x y) := by grind
  clear eq20
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq23 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq22
  have eq24 : (σ x) = (σ x) := by grind
  have eq25 : (σ x) = (σ x) := by grind
  clear eq24
  have eq26 : (σ y) = (σ y) := by grind
  have eq27 : (σ y) = (σ y) := by grind
  clear eq26
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq29 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq28
  have eq30 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq32 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq53 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq16
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq31
    | (have j0 := eq31 (σ X0)
       grind)
    | exact resolve eq31 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq47
    | (have j1 := eq31 x
       grind)
    | exact resolve eq47 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53
       have i₂ := eq31 sF2
       grind)
    | exact superpose eq31 eq53
    | (have j1 := eq31 (σ x)
       grind)
    | exact resolve eq53 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40
    | (have j0 := eq40 x
       grind)
    | exact resolve eq40 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq40
    | (have j0 := eq40 y
       grind)
    | exact resolve eq40 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq92
    | exact resolve eq92 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq31 y
       grind)
    | exact superpose eq31 eq74
    | (have j1 := eq31 y
       grind)
    | exact resolve eq74 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq109 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq99
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq99 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq308 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq42
  have eq388 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq389 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq390 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq388 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq388
    | (have j0 := eq388 X0
       grind)
    | exact resolve eq388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq2919 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2926 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2919 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2919
    | (have j0 := eq2919 X0
       grind)
    | exact resolve eq2919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2932 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2926 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2926
    | (have j0 := eq2926 X0
       grind)
    | exact resolve eq2926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq3168 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq3178 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3168 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3168
    | (have j0 := eq3168 X0
       grind)
    | exact resolve eq3168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3193 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq38 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq38 eq3178
    | (have j0 := eq3178 X0
       grind)
    | exact resolve eq3178 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3206 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3193 X0
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq3193
    | (have j0 := eq3193 X0
       grind)
    | exact resolve eq3193 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3193
  have eq3213 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3206 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3206
    | (have j0 := eq3206 X0
       grind)
    | exact resolve eq3206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3206
  have eq3220 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3213 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3213
    | (have j0 := eq3213 X0
       grind)
    | exact resolve eq3213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq5261 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq308 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq308
    | exact resolve eq308 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq5353 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5261 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq5261
    | (have j0 := eq5261 X0
       grind)
    | exact resolve eq5261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261
  have eq15172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq15173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15172
    | exact resolve eq15172 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq15184 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15173
       have r₂ := eq30
       grind)
    | exact resolve eq15173 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15186 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15184 eq66
    | exact resolve eq66 eq15184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq15184
  have eq15190 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15186
  have eq15192 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33 eq15190
    | exact resolve eq15190 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq15368 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15192 eq109
    | exact resolve eq109 eq15192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq15192
  have eq15371 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15368
  have eq15373 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15371
    | exact resolve eq15371 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15371
  have eq15384 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq15373
       grind)
    | exact superpose eq15373 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15392 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15384
  have eq15418 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq15392
       grind)
    | exact superpose eq15392 eq65
    | exact resolve eq65 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15420 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15392
  have eq15423 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15418
  have eq15424 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15420
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15420
    | exact resolve eq15420 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420
  have eq15425 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15423
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15423
    | exact resolve eq15423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15423
  have eq15644 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15424
       grind)
    | exact superpose eq15424 eq48
    | exact resolve eq48 eq15424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424
  have eq15664 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15644
    | exact resolve eq15644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15644
  have eq15684 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15425 eq3220
    | (have j0 := eq3220 (σ x)
       grind)
    | exact resolve eq3220 eq15425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq15685 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15684
    | exact resolve eq15684 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq70684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq15664
    | exact resolve eq15664 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664 eq15685
  have eq70687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70684
  have eq70696 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70687
       have r₂ := eq30
       grind)
    | exact resolve eq70687 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70687
  have eq70703 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq70729 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70703 eq15425
    | exact resolve eq15425 eq70703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15425 eq70703
  have eq70748 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq70729
  have eq70765 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70748 eq70696
    | exact resolve eq70696 eq70748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70696 eq70748
  have eq70770 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq70765
  have eq70788 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq70770
       grind)
    | exact superpose eq70770 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq70770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70796 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq70788
  have eq71558 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq70796
  have eq72325 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70770
       have i₂ := eq71558
       grind)
    | exact superpose eq71558 eq70770
    | exact resolve eq70770 eq71558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70770 eq71558
  have eq72332 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72325
  have eq72344 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72332
       grind)
    | exact superpose eq72332 eq94
    | exact resolve eq94 eq72332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72345 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72332
  have eq72347 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72344
  have eq72349 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72345
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72345
    | exact resolve eq72345 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72345
  have eq72350 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72347
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72347
    | exact resolve eq72347 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72347
  have eq72973 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72350
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq72350
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq72350 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48
       have i₂ := eq72349
       grind)
    | exact superpose eq72349 eq48
    | exact resolve eq48 eq72349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72349
  have eq76760 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq76717
    | exact resolve eq76717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76717
  have eq76766 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq72973
  have eq104957 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq76766 eq72350
    | exact resolve eq72350 eq76766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72350 eq76766
  have eq105008 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq104957
  have eq105736 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105008
  have eq105740 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq105736
    | exact resolve eq105736 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105736
  have eq106141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq105740 eq76760
    | exact resolve eq76760 eq105740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106141
  have eq106155 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq106144
       have r₂ := eq30
       grind)
    | exact resolve eq106144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106144
  have eq106161 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq106155
  have eq106165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq106161
    | exact resolve eq106161 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106161
  have eq106187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106165 eq76760
    | exact resolve eq76760 eq106165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76760 eq106165
  have eq106190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106187
  have eq106201 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106190
       have r₂ := eq30
       grind)
    | exact resolve eq106190 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106190
  have eq106207 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106201
  have eq106212 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106207
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106207
    | exact resolve eq106207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106207
  have eq107094 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48
       have i₂ := eq106212
       grind)
    | exact superpose eq106212 eq48
    | exact resolve eq48 eq106212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106212
  have eq107137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107094
    | exact resolve eq107094 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107094
  have eq108073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq107137 eq105740
    | exact resolve eq105740 eq107137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105740
  have eq108078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq108073
  have eq108096 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108078
       have r₂ := eq30
       grind)
    | exact resolve eq108078 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108078
  have eq108165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq108096
  have eq108169 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108165
    | exact resolve eq108165 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108165
  have eq108928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq108169 eq107137
    | exact resolve eq107137 eq108169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107137 eq108169
  have eq108931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108928
  have eq108944 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq108931
       have r₂ := eq30
       grind)
    | exact resolve eq108931 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108931
  have eq108949 : (k x x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq109658 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq108949
       grind)
    | exact superpose eq108949 eq47
    | exact resolve eq47 eq108949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq109671 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15373
       have i₂ := eq108949
       grind)
    | exact superpose eq108949 eq15373
    | exact resolve eq15373 eq108949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373 eq108949
  have eq109708 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq109671
  have eq109722 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109658
       have i₂ := eq108944
       grind)
    | exact superpose eq108944 eq109658
    | exact resolve eq109658 eq108944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109658
  have eq109845 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq109722
  have eq109851 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109845
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq109845
    | exact resolve eq109845 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109845
  have eq109889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109851 eq2932
    | (have j0 := eq2932 (σ x)
       grind)
    | (have r₁ := eq2932 (σ x)
       have r₂ := eq109851
       grind)
    | exact resolve eq2932 eq109851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932 eq109851
  have eq109894 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq109889
  have eq2132509 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108944
       have i₂ := eq109708
       grind)
    | exact superpose eq109708 eq108944
    | exact resolve eq108944 eq109708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109708
  have eq2133851 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2132509
  have eq2136497 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq2133851
       grind)
    | exact superpose eq2133851 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq2133851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2136510 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2136497
  have eq2136632 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2136510
  have eq2140981 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2133851
       have i₂ := eq2136632
       grind)
    | exact superpose eq2136632 eq2133851
    | exact resolve eq2133851 eq2136632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133851 eq2136632
  have eq2140992 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2140981
  have eq2141047 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2140992
       grind)
    | exact superpose eq2140992 eq94
    | exact resolve eq94 eq2140992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2141057 : (σ (M.op x y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5353 y
       have i₂ := eq2140992
       grind)
    | exact superpose eq2140992 eq5353
    | exact resolve eq5353 eq2140992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353 eq2140992
  have eq2141070 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2141047
  have eq2141075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2141057
       have i₂ := eq48
       grind)
    | exact superpose eq48 eq2141057
    | exact resolve eq2141057 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq2141057
  have eq2141083 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2141070
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2141070
    | exact resolve eq2141070 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141070
  have eq2141085 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2141075
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2141075
    | exact resolve eq2141075 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141075
  have eq2141089 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23 eq2141085
    | exact resolve eq2141085 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141085
  have eq2143211 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2141083
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq2141083
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq2141083 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2163508 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2143211
  have eq2322198 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2163508 eq2141083
    | exact resolve eq2141083 eq2163508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141083 eq2163508
  have eq2322319 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2322198
  have eq2325746 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2322319
  have eq2325757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2325746
    | exact resolve eq2325746 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325746
  have eq2330274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2325757 eq2141089
    | exact resolve eq2141089 eq2325757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141089 eq2325757
  have eq2330279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2330274
  have eq2330296 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2330279
       have r₂ := eq30
       grind)
    | exact resolve eq2330279 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330279
  have eq2330307 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq2330296 eq109894
    | exact resolve eq109894 eq2330296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109894 eq2330296
  have eq2331583 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2330307
  have eq2335453 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108944
       have i₂ := eq2331583
       grind)
    | exact superpose eq2331583 eq108944
    | exact resolve eq108944 eq2331583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108944 eq2331583
  have eq2336801 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2335453
  have eq2337390 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2336801 eq33
    | exact resolve eq33 eq2336801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2336801
  have eq2337873 : x = y ∨ x = y := by
    first
    | exact superpose eq32 eq2337390
    | exact resolve eq2337390 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2337390
  have eq2337874 : x = y := by grind
  clear eq2337873
  have eq2337880 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2337874
       grind)
    | exact superpose eq2337874 eq21
    | exact resolve eq21 eq2337874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2337881 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2337874
       grind)
    | exact superpose eq2337874 eq27
    | exact resolve eq27 eq2337874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2337874
  have eq2339067 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2337881
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2337881
    | exact resolve eq2337881 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337881
  have eq2339074 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2339067 eq29
    | exact resolve eq29 eq2339067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2339067
  have eq2339628 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq2337880
       grind)
    | exact superpose eq2337880 eq65
    | exact resolve eq65 eq2337880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2340324 : (k x (M.op x y)) = (M.op x (M.op x y)) := by grind
  have eq2340337 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2339628
    | exact resolve eq2339628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339628
  have eq2341009 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2341542 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2340337 eq31
    | (have j0 := eq31 (σ x)
       grind)
    | exact resolve eq31 eq2340337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2341561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2341542
    | exact resolve eq2341542 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341542
  have eq2341611 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2341561
       have r₂ := eq30
       grind)
    | exact resolve eq2341561 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341561
  have eq2341636 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2341611
    | exact resolve eq2341611 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341611
  have eq2346585 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2341636 eq2341009
    | exact resolve eq2341009 eq2341636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341009 eq2341636
  have eq2346587 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2346585
    | exact resolve eq2346585 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346585
  have eq2353327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2346587 eq2340337
    | exact resolve eq2340337 eq2346587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340337 eq2346587
  have eq2353341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2353327
  have eq2353348 : x = (M.op x y) := by
    first
    | (have r₁ := eq2353341
       have r₂ := eq30
       grind)
    | exact resolve eq2353341 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353341
  have eq2353404 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2353348 eq23
    | exact resolve eq23 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2354285 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2353348 eq2340324
    | exact resolve eq2340324 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340324
  have eq2354288 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2354285
       have i₂ := eq2337880
       grind)
    | exact superpose eq2337880 eq2354285
    | exact resolve eq2354285 eq2337880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337880 eq2354285
  have eq2354870 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2353404
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2353404
    | exact resolve eq2353404 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353404
  have eq2354872 : x = (k x x) := by
    first
    | exact superpose eq2353348 eq2354288
    | exact resolve eq2354288 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353348 eq2354288
  have eq2357986 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq2354872
       grind)
    | exact superpose eq2354872 eq389
    | (have j0 := eq389 x
       grind)
    | exact resolve eq389 eq2354872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq2354872
  have eq2358004 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2357986
  have eq2358021 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2358004
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2358004
    | exact resolve eq2358004 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2358004
  have eq2358112 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2339074 eq2358021
    | exact resolve eq2358021 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339074 eq2358021
  have eq2358198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2354870 eq2358112
    | exact resolve eq2358112 eq2354870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354870 eq2358112
  have eq2358282 : False := by grind
  exact eq2358282
