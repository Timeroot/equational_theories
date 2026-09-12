import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) X1) X2) ∨ (k X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X0) X1) X2)
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq87 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 X3 X4
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq61 X2 X1 X2
       have i₂ := eq61 X2 X2 X2
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 X3 (M.op X0 X0)
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq63 X1 X1 (M.op X1 X2)
       have i₂ := eq61 X1 X1 X2
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X3
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq9 X1 (M.op X1 X2) X2
       have i₂ := eq61 X1 X1 X2
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X3 X3) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X3 (M.op X0 X0) X4
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq63 X0 (M.op X2 X2) X2
       have i₂ := eq61 X2 X2 X2
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X0) X3 X4
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq61 X2 X2 X2
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) (M.op X1 X2)) ∨ (M.op (M.op X0 X1) (M.op X1 X2)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq12 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq12
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq61 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 X0 X3 X4
       have i₂ := eq61 X0 X1 X2
       grind)
    | (have i₁ := eq65 X2 X1 X2
       have i₂ := eq61 X2 X2 X2
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq232 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X1) X2) X3
       have i₂ := eq65 X0 X1 X2
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq359 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 X0 X1 x (M.op X0 X1)
       have i₂ := eq87 (M.op X0 X1) (M.op X0 X1) (M.op X1 x) X2 X3
       grind)
    | (have i₁ := eq101 X0 X1 x (M.op X0 X1)
       have i₂ := eq87 (M.op X0 X1) X2 X3 (M.op X0 X1) (M.op X1 x)
       grind)
    | exact superpose eq87 eq101
    | exact resolve eq101 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op (M.op (M.op X3 (M.op X0 X4)) (M.op (M.op X0 X1) (M.op X1 X2))) (M.op (M.op X3 X3) X6)) = X3 := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq103 X3 (M.op X0 X4) (M.op X4 x) X6
       have i₂ := eq87 X0 X4 x X1 X2
       grind)
    | (have i₁ := eq103 X3 (M.op X0 X4) (M.op X4 x) X6
       have i₂ := eq87 X0 X1 X2 X4 x
       grind)
    | exact superpose eq87 eq103
    | exact resolve eq103 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq232 (M.op X0 X1) (M.op X1 x) (M.op (M.op X0 X0) x) X4
       have i₂ := eq103 X0 X1 x x
       grind)
    | exact superpose eq103 eq232
    | exact resolve eq232 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq232
  have eq567 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) (M.op (M.op X1 X4) X5)) = X1 := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq213 X1 (M.op (M.op X0 X0) X2) (M.op X2 x) X4 X5
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq213
    | exact resolve eq213 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X1)
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq359 (M.op X0 X0) X1 (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq359
    | exact resolve eq359 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X1) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq420 X0 X1 X3
       have i₂ := eq420 X0 X1 X2
       grind)
    | (have i₁ := eq420 X0 x x
       have i₂ := eq420 X0 x x
       grind)
    | exact superpose eq420 eq420
    | exact resolve eq420 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq909 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq909 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq909
    | (have j0 := eq909 (σ X0) (σ X1)
       grind)
    | exact resolve eq909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq909 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq909
    | (have j0 := eq909 (τ X0) (τ X1)
       grind)
    | exact resolve eq909 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq909 (τ X1) X0
       grind)
    | exact superpose eq909 eq17
    | (have j1 := eq909 (τ X1) X0
       grind)
    | exact resolve eq17 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq984 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq910 X1 X0
       have i₂ := eq909 X1 X0
       grind)
    | exact superpose eq909 eq910
    | (have j0 := eq910 X1 X0
       have j1 := eq909 (σ X1) (σ X0)
       grind)
    | exact resolve eq910 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1305 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X4)) X5) (M.op X5 X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq108 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X0 X4 X5 X6
       have i₂ := eq359 X0 X1 X2 X3
       grind)
    | exact superpose eq359 eq108
    | exact resolve eq108 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1507 : ∀ X0 X1 X4 X5 X6 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X4)) X5) (M.op X5 X6)) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq1305 X0 X1 x x X4 X5 X6
       have i₂ := eq213 (M.op X0 X1) x x x (M.op x x)
       grind)
    | exact superpose eq213 eq1305
    | exact resolve eq1305 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq1305
  have eq1676 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (M.op (M.op (τ X1) (τ X1)) X2)))) ∨ (τ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq930 (M.op (M.op X1 X1) (M.op (M.op (τ X1) (τ X1)) X2)) X1
       have i₂ := eq63 (τ X1) X1 X2
       grind)
    | exact superpose eq63 eq930
    | exact resolve eq930 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq2573 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 X1 (M.op X0 X0) x (M.op x x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq631
    | exact resolve eq631 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq2786 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 X0 (M.op X1 X1)
       have i₂ := eq2573 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq63 X0 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq2573 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq2573 eq63
    | exact resolve eq63 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2573
  have eq2958 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2786 X0 X1
       have i₂ := eq680 X0 (M.op X1 X1) X0 X2
       grind)
    | (have i₁ := eq2786 X0 X1
       have i₂ := eq680 X0 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq680 eq2786
    | exact resolve eq2786 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq2786
  have eq3145 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X1 X2
       have i₂ := eq2958 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq2958 eq9
    | exact resolve eq9 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3239 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3145 X0 X1 X2
       have i₂ := eq3145 X0 X1 X3
       grind)
    | (have i₁ := eq3145 X0 X2 X2
       have i₂ := eq3145 X0 X2 X2
       grind)
    | exact superpose eq3145 eq3145
    | exact resolve eq3145 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3296 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2958 X0 X1 X3
       have i₂ := eq3145 X0 X1 X2
       grind)
    | (have i₁ := eq2958 X0 X2 X2
       have i₂ := eq3145 X0 X2 X2
       grind)
    | exact superpose eq3145 eq2958
    | exact resolve eq2958 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958 eq3145
  have eq3657 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 X1 X2 x X0
       have i₂ := eq3239 (M.op X0 X0) (M.op X1 X2) X3 (M.op X2 x)
       grind)
    | (have i₁ := eq101 X1 X2 x X0
       have i₂ := eq3239 (M.op X0 X0) (M.op X1 X2) (M.op X2 x) X3
       grind)
    | exact superpose eq3239 eq101
    | exact resolve eq101 eq3239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq3239
  have eq4178 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3657 (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) X1 X2 X3
       have i₂ := eq3296 X0 (M.op (M.op X1 X2) X3) X4 (M.op (M.op (M.op X1 X2) X3) X4)
       grind)
    | exact superpose eq3296 eq3657
    | exact resolve eq3657 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3657
  have eq4719 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq616 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq4720 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq4178 (M.op X0 X1) X0 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq4178 eq4719
    | (have j0 := eq4719 X0 X1
       grind)
    | exact resolve eq4719 eq4178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq8959 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X2 (M.op (M.op X0 X1) X4)) (M.op (M.op (M.op X0 X1) (M.op X0 X3)) (M.op (M.op X0 X1) (M.op X0 X3)))) (M.op (M.op X2 X5) X6)) = X2 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq567 (M.op (M.op (M.op X0 X1) (M.op X0 X3)) (M.op (M.op X0 X1) (M.op X0 X3))) X2 X4 X5 X6
       have i₂ := eq1507 X0 X1 X3 (M.op (M.op X0 X1) (M.op X0 X3)) (M.op (M.op X0 X1) (M.op X0 X3))
       grind)
    | exact superpose eq1507 eq567
    | exact resolve eq567 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1507
  have eq9028 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X0) (M.op (M.op X2 X5) X6)) = X2 := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq8959 X0 X1 X2 x X4 X5 X6
       have i₂ := eq4178 (M.op X2 (M.op (M.op X0 X1) X4)) X0 X1 (M.op X0 x) (M.op (M.op X0 X1) (M.op X0 x))
       grind)
    | exact superpose eq4178 eq8959
    | exact resolve eq8959 eq4178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4178 eq8959
  have eq10377 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq106 X0 X1 X1 X1 x
       have i₂ := eq87 (M.op X0 X1) (M.op X1 X1) x X2 X3
       grind)
    | (have i₁ := eq106 X0 X1 X1 X1 x
       have i₂ := eq87 (M.op X0 X1) X2 X3 (M.op X1 X1) x
       grind)
    | exact superpose eq87 eq106
    | exact resolve eq106 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq10980 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) X4) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq10377 X0 (M.op (M.op X1 X2) X3) X1 X2
       have i₂ := eq87 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) (M.op X1 X2) X3 X4 X5
       grind)
    | (have i₁ := eq10377 X0 (M.op (M.op X1 X2) X3) X1 X2
       have i₂ := eq87 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) X4 X5 (M.op X1 X2) X3
       grind)
    | exact superpose eq87 eq10377
    | exact resolve eq10377 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq10990 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X1) X4) (M.op X4 X5)) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 X0 X4 X5
       have i₂ := eq10377 X0 X1 X2 X3
       grind)
    | exact superpose eq10377 eq9
    | exact resolve eq9 eq10377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq984 x y
       grind)
    | exact superpose eq984 eq16
    | (have j1 := eq984 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq984 x y
       grind)
    | exact resolve eq16 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq17019 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16941
  have eq17031 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17019
       grind)
    | exact superpose eq17019 eq16
    | exact resolve eq16 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17032 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq17019
       grind)
    | exact superpose eq17019 eq9
    | exact resolve eq9 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17033 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq17019
       grind)
    | exact superpose eq17019 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17019
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17019
       grind)
    | exact resolve eq12 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17061 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) (M.op X0 X1)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3296 X0 (σ x) (σ y) X1
       have i₂ := eq17019
       grind)
    | exact superpose eq17019 eq3296
    | exact resolve eq3296 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq17092 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17033
  have eq17095 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17092
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17092
    | exact resolve eq17092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092
  have eq18151 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq911 X0 X1
       grind)
    | exact superpose eq911 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq911 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq911 X0 X1
       grind)
    | exact resolve eq12 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq18214 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18151 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq18151 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq18151 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18151
  have eq18221 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18214 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq18214
    | (have j0 := eq18214 X0 X1
       grind)
    | exact resolve eq18214 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18214
  have eq18307 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18221 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18221
    | (have j0 := eq18221 (σ X0) (σ X1)
       grind)
    | exact resolve eq18221 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18221
  have eq18324 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18307 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq18307
    | (have j0 := eq18307 X0 X1
       grind)
    | exact resolve eq18307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18307
  have eq18329 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18324 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18324
    | (have j0 := eq18324 X0 X1
       grind)
    | exact resolve eq18324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18324
  have eq18333 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (τ (k (σ X1) (σ X0))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18329 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq18329
    | (have j0 := eq18329 X0 X1
       grind)
    | exact resolve eq18329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18329
  have eq18336 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18333 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq18333
    | (have j0 := eq18333 X0 X1
       grind)
    | exact resolve eq18333 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18333
  have eq18339 : ∀ X0 X1 : G, (k X1 X0) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18336 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq18336
    | (have j0 := eq18336 X0 X1
       grind)
    | exact resolve eq18336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18336
  have eq18341 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18339 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18339
    | (have j0 := eq18339 X0 X1
       grind)
    | exact resolve eq18339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18339
  have eq18344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18341 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18341
    | (have j0 := eq18341 (σ X0) (σ X1)
       grind)
    | exact resolve eq18341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18341
  have eq18356 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18344 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18344
    | (have j0 := eq18344 X0 X1
       grind)
    | exact resolve eq18344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344
  have eq18588 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18356 x y
       have i₂ := eq17095
       grind)
    | exact superpose eq17095 eq18356
    | (have j0 := eq18356 x y
       grind)
    | exact resolve eq18356 eq17095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17095 eq18356
  have eq18589 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17019 eq18588
    | exact resolve eq18588 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18588
  have eq18604 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq909 eq18589
    | (have j1 := eq909 y x
       grind)
    | (have r₁ := eq18589
       have r₂ := eq909 (σ x) (σ y)
       grind)
    | exact resolve eq18589 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18589
  have eq18616 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18604
       have r₂ := eq17031
       grind)
    | exact resolve eq18604 eq17031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17031 eq18604
  have eq18690 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17061 (σ x) (σ y)
       have i₂ := eq17019
       grind)
    | exact superpose eq17019 eq17061
    | exact resolve eq17061 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17061
  have eq18806 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq18690
  have eq26766 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq69 X0 (σ x) (σ y)
       have i₂ := eq17032 X0
       grind)
    | exact superpose eq17032 eq69
    | exact resolve eq69 eq17032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq17032
  have eq26770 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq26766 X0
       have j1 := eq909 X0 X0
       grind)
    | (have r₁ := eq26766 X0
       have r₂ := eq909 X0 X0
       grind)
    | exact resolve eq26766 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26766
  have eq26815 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26770 (σ X0)
       grind)
    | exact superpose eq26770 eq15
    | exact resolve eq15 eq26770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26834 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26770 eq26815
    | exact resolve eq26815 eq26770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26770 eq26815
  have eq26998 : (σ x) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26834 eq18806
    | exact resolve eq18806 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18806
  have eq43087 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ y) (σ y)) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4720 (σ x) (σ y)
       have i₂ := eq17019
       grind)
    | exact superpose eq17019 eq4720
    | exact resolve eq4720 eq17019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq43194 : (σ (M.op y y)) = (k (σ y) (M.op (σ (M.op y y)) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26834 eq43087
    | exact resolve eq43087 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43087
  have eq43256 : (σ (M.op y y)) = (k (σ y) (M.op (σ (M.op y y)) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26834 eq43194
    | exact resolve eq43194 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26834 eq43194
  have eq43306 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26998 eq43256
    | exact resolve eq43256 eq26998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43256
  have eq43333 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43306
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq43306
    | exact resolve eq43306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43306
  have eq43344 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26998 eq43333
    | exact resolve eq43333 eq26998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26998 eq43333
  have eq43349 : (σ (k y x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43344
       have r₂ := eq18616
       grind)
    | exact resolve eq43344 eq18616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43344
  have eq43353 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq909 eq43349
    | (have j1 := eq909 y x
       grind)
    | exact resolve eq43349 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq43349
  have eq43366 : (M.op y y) = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq43353
       grind)
    | exact superpose eq43353 eq10
    | exact resolve eq10 eq43353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43353
  have eq43412 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43366
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq43366
    | exact resolve eq43366 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43366
  have eq43519 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) (M.op X0 X1)) y) X2) (M.op X2 X3)) ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10990 y y X0 X1 X2 X3
       have i₂ := eq43412
       grind)
    | exact superpose eq43412 eq10990
    | exact resolve eq10990 eq43412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43412
  have eq43559 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq43519 x x x x
       have i₂ := eq10990 x y x x x x
       grind)
    | exact superpose eq10990 eq43519
    | exact resolve eq43519 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10990 eq43519
  have eq43572 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43559 eq17019
    | exact resolve eq17019 eq43559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17019
  have eq43580 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43559 eq18616
    | exact resolve eq18616 eq43559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18616 eq43559
  have eq43682 : y = (M.op x y) := by
    first
    | (have r₁ := eq43572
       have r₂ := eq43580
       grind)
    | exact resolve eq43572 eq43580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43572 eq43580
  have eq43685 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq16
    | exact resolve eq16 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43686 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq9
    | exact resolve eq9 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43688 : y ≠ y ∨ x = (M.op y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq43682
       grind)
    | exact resolve eq13 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43709 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y X0) (M.op X0 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq359 x y x x
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq359
    | exact resolve eq359 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq43745 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) x) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10377 X0 X1 x y
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq10377
    | exact resolve eq10377 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10377
  have eq43774 : (k y x) = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq43688
  have eq44516 : y = (M.op (M.op (M.op y x) y) x) := by
    first
    | (have i₁ := eq43709 x y
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq43709
    | exact resolve eq43709 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43709
  have eq47454 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq910 y x
       have i₂ := eq43774
       grind)
    | exact superpose eq43774 eq910
    | (have j0 := eq910 y x
       grind)
    | exact resolve eq910 eq43774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq43774
  have eq47464 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq47454
       have r₂ := eq43685
       grind)
    | exact resolve eq47454 eq43685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47454
  have eq144411 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (M.op X0 X0) (M.op (M.op (τ (σ X1)) (τ (σ X1))) X2))))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 (σ (M.op (M.op X0 X0) (M.op (M.op (τ (σ X1)) (τ (σ X1))) X2)))
       have i₂ := eq1676 X0 (σ X1) X2
       grind)
    | exact superpose eq1676 eq28
    | (have j1 := eq1676 (k X1 (τ (σ (M.op (M.op X0 X0) (M.op (M.op (τ (σ X1)) (τ (σ X1))) X2))))) (σ X0) X2
       grind)
    | exact resolve eq28 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1676
  have eq144479 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 (M.op (M.op X0 X0) (M.op (M.op (τ (σ X1)) (τ (σ X1))) X2))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144411 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op (M.op (τ (σ X1)) (τ (σ X1))) X2))
       grind)
    | exact superpose eq10 eq144411
    | (have j0 := eq144411 (k X1 (M.op (M.op X0 X0) (M.op (M.op (τ (σ X1)) (τ (σ X1))) X2))) X0 X2
       grind)
    | exact resolve eq144411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144411
  have eq144605 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144479 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144479
    | (have j0 := eq144479 (k X1 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) X0 X2
       grind)
    | exact resolve eq144479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144479
  have eq144678 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144605 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144605
    | (have j0 := eq144605 X0 X1 X2
       grind)
    | exact resolve eq144605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144605
  have eq144706 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144678 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq144678
    | (have j0 := eq144678 X0 X1 X2
       grind)
    | exact resolve eq144678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144678
  have eq145973 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144706 (M.op (M.op X0 X0) (M.op X0 X1)) (M.op X0 X0) x
       have i₂ := eq387 X0 X0 X1 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq387 eq144706
    | (have j0 := eq144706 (M.op (M.op X0 X0) (M.op X0 X1)) (k (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact resolve eq144706 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq144706
  have eq146060 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq145973 X0 X1
       have j1 := eq109 X0 X0 X1
       grind)
    | (have r₁ := eq145973 X1 x
       have r₂ := eq109 X1 X1 x
       grind)
    | exact resolve eq145973 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq145973
  have eq148837 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (k (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1)) (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10980 X0 X1 X2 X3 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) x
       have i₂ := eq146060 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X1) x
       grind)
    | exact superpose eq146060 eq10980
    | exact resolve eq10980 eq146060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10980 eq146060
  have eq149173 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq148837 x x x x
       have i₂ := eq9028 x x x x (M.op (M.op x x) x) x
       grind)
    | exact superpose eq9028 eq148837
    | exact resolve eq148837 eq9028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9028 eq148837
  have eq149454 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq149173 (σ X0)
       grind)
    | exact superpose eq149173 eq15
    | exact resolve eq15 eq149173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149507 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq149454 X0
       have i₂ := eq149173 X0
       grind)
    | exact superpose eq149173 eq149454
    | exact resolve eq149454 eq149173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149173 eq149454
  have eq149856 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) x) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq149507 X0
       have i₂ := eq43745 (σ X0) X1
       grind)
    | exact superpose eq43745 eq149507
    | exact resolve eq149507 eq43745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43745
  have eq149894 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) x) y) := by
    intro X0
    first
    | (have i₁ := eq43686 (σ X0)
       have i₂ := eq149507 X0
       grind)
    | exact superpose eq149507 eq43686
    | exact resolve eq43686 eq149507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43686
  have eq169895 : (σ (M.op x x)) = (M.op (M.op (M.op (σ (M.op y y)) x) y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq149856 x (σ y)
       have i₂ := eq47464
       grind)
    | exact superpose eq47464 eq149856
    | exact resolve eq149856 eq47464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47464 eq149856
  have eq170541 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq169895
       have i₂ := eq149894 y
       grind)
    | exact superpose eq149894 eq169895
    | exact resolve eq169895 eq149894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169895
  have eq170648 : (σ (M.op y y)) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq170541
       have i₂ := eq149507 y
       grind)
    | exact superpose eq149507 eq170541
    | exact resolve eq170541 eq149507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170541
  have eq170696 : (σ y) = (M.op (M.op (σ (M.op x x)) x) y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq149894 y
       have i₂ := eq170648
       grind)
    | exact superpose eq170648 eq149894
    | exact resolve eq149894 eq170648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170648
  have eq170843 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170696
       have i₂ := eq149894 x
       grind)
    | exact superpose eq149894 eq170696
    | exact resolve eq170696 eq149894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149894 eq170696
  have eq170866 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44516
       have i₂ := eq170843
       grind)
    | exact superpose eq170843 eq44516
    | exact resolve eq44516 eq170843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44516
  have eq171186 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170866
       have i₂ := eq43682
       grind)
    | exact superpose eq43682 eq170866
    | exact resolve eq170866 eq43682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170866
  have eq171243 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq170843 eq171186
    | exact resolve eq171186 eq170843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170843 eq171186
  have eq171290 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq171243
       grind)
    | exact superpose eq171243 eq10
    | exact resolve eq10 eq171243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171243
  have eq171422 : x = y ∨ x = y := by
    first
    | (have i₁ := eq171290
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq171290
    | exact resolve eq171290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171290
  have eq171423 : x = y := by grind
  clear eq171422
  have eq171428 : x = (M.op x x) := by
    first
    | (have i₁ := eq43682
       have i₂ := eq171423
       grind)
    | exact superpose eq171423 eq43682
    | exact resolve eq43682 eq171423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43682
  have eq171429 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43685
       have i₂ := eq171423
       grind)
    | exact superpose eq171423 eq43685
    | exact resolve eq43685 eq171423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43685 eq171423
  have eq171553 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq171429
       have i₂ := eq149507 x
       grind)
    | exact superpose eq149507 eq171429
    | exact resolve eq171429 eq149507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149507 eq171429
  have eq171708 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq171553
       have i₂ := eq171428
       grind)
    | exact superpose eq171428 eq171553
    | exact resolve eq171553 eq171428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171428 eq171553
  have eq171709 : False := by grind
  exact eq171709

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
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
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq112 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq131 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq84 (σ X1) (σ X0)
       grind)
    | exact superpose eq84 eq15
    | (have j1 := eq84 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X0 X3 X4
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq23 X2 X1 X2
       have i₂ := eq23 X2 X2 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq23 (M.op X0 X1) (M.op X1 X2) X2
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X0 X3 (M.op X0 X0)
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq25 X1 X1 (M.op X1 X2)
       have i₂ := eq23 X1 X1 X2
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X3
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq9 X1 (M.op X1 X2) X2
       have i₂ := eq23 X1 X1 X2
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X3 X3) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X0 X0) X4
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq25 X0 (M.op X2 X2) X2
       have i₂ := eq23 X2 X2 X2
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq238 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op X0 X0)) (M.op (M.op X0 X1) (M.op X1 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq23 X0 X1 X2
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq210 X0 X1 X2 x
       have i₂ := eq230 X0 X1 X2 x
       grind)
    | exact superpose eq230 eq210
    | exact resolve eq210 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq831 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq90 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq886 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq831 X0 X1
       have j1 := eq131 X1 (σ X0)
       grind)
    | (have r₁ := eq831 X0 X0
       have r₂ := eq131 X0 (σ X0)
       grind)
    | exact resolve eq831 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq831
  have eq907 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq886
    | (have j0 := eq886 X0 X1
       grind)
    | exact resolve eq886 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq922 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq907
    | (have j0 := eq907 X0 X1
       grind)
    | exact resolve eq907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq923 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq922 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1918 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq228 X0 X1 x (M.op X0 X1)
       have i₂ := eq206 (M.op X0 X1) (M.op X0 X1) (M.op X1 x) X2 X3
       grind)
    | (have i₁ := eq228 X0 X1 x (M.op X0 X1)
       have i₂ := eq206 (M.op X0 X1) X2 X3 (M.op X0 X1) (M.op X1 x)
       grind)
    | exact superpose eq206 eq228
    | exact resolve eq228 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq228
  have eq2412 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 (M.op X0 (M.op X1 X1)) X1 x
       have i₂ := eq23 X0 (M.op X1 X1) x
       grind)
    | (have i₁ := eq139 (M.op (M.op X1 X1) (M.op X1 X1)) X1 (M.op X1 X1)
       have i₂ := eq23 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq23 eq139
    | exact resolve eq139 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq139
  have eq3601 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq112 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X1 x) (M.op x x)) X4
       have i₂ := eq238 X1 x x X0
       grind)
    | exact superpose eq238 eq112
    | exact resolve eq112 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq238
  have eq3625 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) X1) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq3601 X0 X1 X4
       have i₂ := eq2412 (M.op X0 X0) X1
       grind)
    | exact superpose eq2412 eq3601
    | exact resolve eq3601 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq3601
  have eq3650 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq3625 X0 X1 X4
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq3625
    | exact resolve eq3625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq5062 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X1 X1) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X3
       have i₂ := eq3650 X0 X1 X2
       grind)
    | (have i₁ := eq9 X1 (M.op X1 x) X2
       have i₂ := eq3650 X1 X1 x
       grind)
    | exact superpose eq3650 eq9
    | exact resolve eq9 eq3650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650
  have eq6063 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X4)) (M.op (M.op X5 X5) X6)) X5) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq237 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) X0 X4 X5 X6
       have i₂ := eq1918 X0 X1 X2 X3
       grind)
    | exact superpose eq1918 eq237
    | exact resolve eq237 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq6558 : ∀ X0 X1 X4 X5 X6 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X4)) (M.op (M.op X5 X5) X6)) X5) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq6063 X0 X1 x x X4 X5 X6
       have i₂ := eq255 (M.op X0 X1) x x
       grind)
    | exact superpose eq255 eq6063
    | exact resolve eq6063 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq6063
  have eq7899 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X1) (σ X1)) = (M.op (M.op (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) X2)) (M.op (M.op X3 X3) X4)) X3) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq237 (σ X1) (σ X0) X2 X3 X4
       have i₂ := eq175 X0 X1
       grind)
    | (have i₁ := eq237 (σ X0) (σ X1) X2 X3 X4
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq237
    | (have j1 := eq175 X0 X1
       grind)
    | exact resolve eq237 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq237
  have eq7927 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7899 X0 X1 x x x
       have i₂ := eq6558 (σ X0) (σ X1) x x x
       grind)
    | exact superpose eq6558 eq7899
    | (have j0 := eq7899 X0 X1 x x x
       grind)
    | exact resolve eq7899 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558 eq7899
  have eq7962 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7927 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq7927
    | (have j0 := eq7927 X0 X1
       grind)
    | exact resolve eq7927 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7927
  have eq7981 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7962 X0 X1
       have j1 := eq923 X0 X1
       grind)
    | (have r₁ := eq7962 X0 X1
       have r₂ := eq923 X0 X1
       grind)
    | exact resolve eq7962 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq7962
  have eq8011 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7981 x y
       grind)
    | exact superpose eq7981 eq16
    | exact resolve eq16 eq7981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7981
  have eq8451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8011
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq8011
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq8011 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq8011
  have eq8454 : (M.op x y) = (M.op y x) := by grind
  clear eq8451
  have eq9177 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op y y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 y x X0 X1
       have i₂ := eq8454
       grind)
    | exact superpose eq8454 eq230
    | exact resolve eq230 eq8454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq8454
  have eq9223 : x = y := by
    first
    | (have i₁ := eq9177 x x
       have i₂ := eq5062 x y x x
       grind)
    | exact superpose eq5062 eq9177
    | exact resolve eq9177 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062 eq9177
  have eq9952 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9223
       grind)
    | exact superpose eq9223 eq16
    | exact resolve eq16 eq9223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9223
  have eq9953 : False := by grind
  exact eq9953

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq67 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq67 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq279 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq77 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq286 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       have j1 := eq71 X1 X0
       grind)
    | (have r₁ := eq279 X1 X0
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq279 X0 X0
       have r₂ := eq71 X0 X0
       grind)
    | exact resolve eq279 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq279
  have eq404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq286 (σ X0) (σ X1)
       grind)
    | exact superpose eq286 eq15
    | exact resolve eq15 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq286 X0 X1
       grind)
    | exact superpose eq286 eq404
    | exact resolve eq404 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq404
  have eq410 : False := by grind
  exact eq410

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq29 : y = (τ (σ y)) := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq104 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq79 sF3 (σ X0)
       grind)
    | exact superpose eq79 eq36
    | (have j1 := eq79 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq107 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq103
    | exact resolve eq103 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq107
    | exact resolve eq107 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq107
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq102
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq102 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq125 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq140
    | exact resolve eq140 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq144 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq141
       have r₂ := eq27
       grind)
    | exact resolve eq141 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq146 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq144
    | exact resolve eq144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq252 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq589 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq505 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq505
    | exact resolve eq505 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq667 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146 eq127
    | (have r₁ := eq127
       have r₂ := eq146
       grind)
    | exact resolve eq127 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq668 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq667
  have eq671 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq668 eq119
    | exact resolve eq119 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq674 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq671
  have eq681 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq674 eq65
    | exact resolve eq65 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq674
  have eq733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq681
       have r₂ := eq146
       grind)
    | exact resolve eq681 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq681
  have eq841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq733 eq119
    | exact resolve eq119 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq733
  have eq844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq841
  have eq848 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq844
       have r₂ := eq27
       grind)
    | exact resolve eq844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq850 : (τ (σ (M.op x y))) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq848 eq133
    | exact resolve eq133 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq855 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq848 eq52
    | exact resolve eq52 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq875 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq850
    | exact resolve eq850 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq880 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op (M.op (M.op x y) X0) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq51 y X1 x
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq51
    | exact resolve eq51 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq875
  have eq2198 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq528 X0
       have i₂ := eq252 x
       grind)
    | exact superpose eq252 eq528
    | exact resolve eq528 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq2245 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq880 eq2198
    | exact resolve eq2198 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq2198
  have eq2311 : ∀ X0 : G, (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq252 sF2
       grind)
    | exact superpose eq252 eq529
    | exact resolve eq529 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq2750 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2245 eq14
    | exact resolve eq14 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq3508 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2750 eq252
    | exact resolve eq252 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq3544 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52 eq3508
    | exact resolve eq3508 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508
  have eq3737 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq3544
       grind)
    | exact superpose eq3544 eq74
    | exact resolve eq74 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq3776 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3737
    | exact resolve eq3737 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq3866 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3776 eq52
    | exact resolve eq52 eq3776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq4478 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq429 X0 X1 X2
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq429
    | exact resolve eq429 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq429
  have eq4812 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3866 eq855
    | exact resolve eq855 eq3866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq3866
  have eq4828 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4812
  have eq4832 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4828 eq26
    | exact resolve eq26 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq4977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4832 eq3776
    | exact resolve eq3776 eq4832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776 eq4832
  have eq5036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4977
  have eq5054 : x = (M.op x y) := by
    first
    | (have r₁ := eq5036
       have r₂ := eq27
       grind)
    | exact resolve eq5036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036
  have eq5056 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5054 eq20
    | exact resolve eq20 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5060 : x ≠ x ∨ x = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq5054 eq126
    | (have r₁ := eq126
       have r₂ := eq5054
       grind)
    | exact resolve eq126 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq5069 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) x) := by
    intro X0
    first
    | exact superpose eq5054 eq2311
    | exact resolve eq2311 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311
  have eq5073 : x = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq5060
  have eq5083 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5056
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5056
    | exact resolve eq5056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5056
  have eq5794 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5083 eq26
    | exact resolve eq26 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5911 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq5794 eq4478
    | exact resolve eq4478 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq5912 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq5054 eq5911
    | exact resolve eq5911 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5911
  have eq9257 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq105
    | (have j0 := eq105 (M.op x y)
       grind)
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105
  have eq9289 : (M.op (σ x) (σ y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5794 eq9257
    | exact resolve eq9257 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9257
  have eq9316 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq104 eq9289
    | exact resolve eq9289 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq9289
  have eq9328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq5794 eq9316
    | exact resolve eq9316 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9316
  have eq9332 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq9328
       have r₂ := eq27
       grind)
    | exact resolve eq9328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9328
  have eq9345 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq9332 eq125
    | exact resolve eq125 eq9332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq9332
  have eq9348 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5054 eq9345
    | exact resolve eq9345 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9345
  have eq9712 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ (M.op x y)) x) x) := by
    intro X0
    first
    | exact superpose eq5083 eq5069
    | exact resolve eq5069 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq10224 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq9712 eq5912
    | exact resolve eq5912 eq9712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5912 eq9712
  have eq24942 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5073
       have i₂ := eq9348
       grind)
    | exact superpose eq9348 eq5073
    | exact resolve eq5073 eq9348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073
  have eq25047 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq24942
       grind)
    | exact superpose eq24942 eq109
    | exact resolve eq109 eq24942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq24942
  have eq25163 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25047
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq25047
    | exact resolve eq25047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25047
  have eq25265 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25163 eq589
    | exact resolve eq589 eq25163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq25163
  have eq25290 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10224 eq25265
    | exact resolve eq25265 eq10224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10224 eq25265
  have eq25305 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq25290
       grind)
    | exact superpose eq25290 eq64
    | exact resolve eq64 eq25290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq25290
  have eq25466 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq25305
       have r₂ := eq5054
       grind)
    | exact resolve eq25305 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25305
  have eq25478 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25466
       have i₂ := eq9348
       grind)
    | exact superpose eq9348 eq25466
    | exact resolve eq25466 eq9348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348 eq25466
  have eq25481 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5054 eq25478
    | exact resolve eq25478 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25478
  have eq25488 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25481 eq15
    | exact resolve eq15 eq25481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25481
  have eq25515 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25488
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25488
    | exact resolve eq25488 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5083 eq25515
    | exact resolve eq25515 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25515
  have eq25518 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq25517
       have r₂ := eq27
       grind)
    | exact resolve eq25517 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25517
  have eq25521 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq25518 eq29
    | exact resolve eq29 eq25518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq25572 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25518 eq5794
    | exact resolve eq5794 eq25518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5794 eq25518
  have eq25596 : y = (M.op x y) := by
    first
    | exact superpose eq30 eq25521
    | exact resolve eq25521 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25521
  have eq25608 : x = y := by
    first
    | exact superpose eq5054 eq25596
    | exact resolve eq25596 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25596
  have eq25615 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25608
       grind)
    | exact superpose eq25608 eq18
    | exact resolve eq18 eq25608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25608
  have eq25680 : x = (M.op x x) := by
    first
    | exact superpose eq5054 eq25615
    | exact resolve eq25615 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054 eq25615
  have eq25946 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq25680
       grind)
    | exact superpose eq25680 eq74
    | exact resolve eq74 eq25680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq25680
  have eq26116 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5083 eq25946
    | exact resolve eq25946 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25946
  have eq26146 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25572 eq26116
    | exact resolve eq26116 eq25572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25572 eq26116
  have eq26156 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26146
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26146
    | exact resolve eq26146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26146
  have eq26159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5083 eq26156
    | exact resolve eq26156 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5083 eq26156
  have eq26161 : False := by grind
  exact eq26161

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq76 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq94
    | (have j0 := eq94 (σ X0) (σ X1)
       grind)
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq44
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq44 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq157 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq832 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq129
  have eq833 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq832
  have eq836 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq833 eq120
    | exact resolve eq120 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq840 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq836
  have eq845 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq840
       have r₂ := eq131
       grind)
    | exact resolve eq840 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq840
  have eq856 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq845 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq845
       grind)
    | exact resolve eq13 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq858 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq856
  have eq866 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq858
    | exact resolve eq858 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq866 eq120
    | exact resolve eq120 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq866
  have eq1007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1004
  have eq1011 : x = (M.op x y) := by
    first
    | (have r₁ := eq1007
       have r₂ := eq27
       grind)
    | exact resolve eq1007 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1013 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1011 eq20
    | exact resolve eq20 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq1011 eq76
    | (have r₁ := eq76
       have r₂ := eq1011
       grind)
    | exact resolve eq76 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1022 : x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq1018
  have eq1028 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1013
    | exact resolve eq1013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1043 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq98
    | (have j0 := eq98 (M.op x y) X0
       grind)
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq98
  have eq1096 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1011 eq1043
    | (have j0 := eq1043 X0
       grind)
    | exact resolve eq1043 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1104 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1028 eq26
    | exact resolve eq26 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1262 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1096 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1096
    | (have j0 := eq1096 y
       grind)
    | exact resolve eq1096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1096
  have eq1275 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1104 eq1262
    | exact resolve eq1262 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1289 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1275
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1275
    | exact resolve eq1275 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1275
  have eq1298 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1028 eq1289
    | exact resolve eq1289 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1104 eq1298
    | exact resolve eq1298 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1298
  have eq1305 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq1303
       have r₂ := eq27
       grind)
    | exact resolve eq1303 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1307 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq1305 eq157
    | exact resolve eq157 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq1305
  have eq1309 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1011 eq1307
    | exact resolve eq1307 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1389 : x = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1022
       have i₂ := eq1309
       grind)
    | exact superpose eq1309 eq1022
    | exact resolve eq1022 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1391 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1389
       grind)
    | exact superpose eq1389 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1389
       grind)
    | exact resolve eq13 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1397 : (M.op x y) = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1391
  have eq1398 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq1309
       grind)
    | exact superpose eq1309 eq1397
    | exact resolve eq1397 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq1397
  have eq1400 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1398
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1398
    | exact resolve eq1398 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1398
  have eq1402 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1011 eq1400
    | exact resolve eq1400 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq1400
  have eq1403 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1402
  have eq1409 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1403 eq15
    | exact resolve eq15 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1410 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1409
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1409
    | exact resolve eq1409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1409
  have eq1411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1028 eq1410
    | exact resolve eq1410 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq1410
  have eq1412 : False := by grind
  exact eq1412

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq914 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq914 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq914
    | (have j0 := eq914 (σ X0) (σ X1)
       grind)
    | exact resolve eq914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2312 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq915 X0 X1
       have i₂ := eq914 X0 X1
       grind)
    | exact superpose eq914 eq915
    | (have j0 := eq915 X0 X1
       have j1 := eq914 (σ X0) (σ X1)
       grind)
    | exact resolve eq915 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2312 x y
       grind)
    | exact superpose eq2312 eq16
    | (have j1 := eq2312 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2312 x y
       grind)
    | exact resolve eq16 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq17099 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17019
  have eq17111 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq16
    | exact resolve eq16 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17114 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17099
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17099
       grind)
    | exact resolve eq13 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17173 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17114
  have eq17177 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17173
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17173
    | exact resolve eq17173 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17173
  have eq17180 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq914 eq17177
    | (have j1 := eq914 (σ y) (σ x)
       grind)
    | exact resolve eq17177 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17177
  have eq17181 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17180
       have r₂ := eq17111
       grind)
    | exact resolve eq17180 eq17111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17180
  have eq17184 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq17181
       grind)
    | exact superpose eq17181 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17181
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17181
       grind)
    | exact resolve eq12 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181
  have eq17244 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17184
  have eq17247 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17244
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17244
    | exact resolve eq17244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17244
  have eq17249 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17099 eq17247
    | exact resolve eq17247 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17099 eq17247
  have eq17251 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq914 eq17249
    | (have j1 := eq914 x y
       grind)
    | exact resolve eq17249 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq17249
  have eq17253 : y = (M.op x y) := by
    first
    | (have r₁ := eq17251
       have r₂ := eq17111
       grind)
    | exact resolve eq17251 eq17111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17111 eq17251
  have eq17255 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17253
       grind)
    | exact superpose eq17253 eq16
    | exact resolve eq16 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17258 : y ≠ y ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17253
       grind)
    | exact superpose eq17253 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17253
       grind)
    | exact resolve eq13 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17316 : y = (k x y) ∨ x = (M.op y x) := by grind
  clear eq17258
  have eq17736 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq915 x y
       have i₂ := eq17316
       grind)
    | exact superpose eq17316 eq915
    | (have j0 := eq915 x y
       grind)
    | exact resolve eq915 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17316
  have eq17739 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq17736
  have eq17741 : x = (M.op y x) := by
    first
    | (have r₁ := eq17739
       have r₂ := eq17255
       grind)
    | exact resolve eq17739 eq17255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17739
  have eq17744 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq17741
       grind)
    | exact superpose eq17741 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17741
       grind)
    | exact resolve eq12 eq17741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17741
  have eq17804 : (M.op x y) = (k x y) := by grind
  clear eq17744
  have eq17828 : y = (k x y) := by
    first
    | (have i₁ := eq17804
       have i₂ := eq17253
       grind)
    | exact superpose eq17253 eq17804
    | exact resolve eq17804 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17253 eq17804
  have eq17844 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq915 x y
       have i₂ := eq17828
       grind)
    | exact superpose eq17828 eq915
    | (have j0 := eq915 x y
       grind)
    | exact resolve eq915 eq17828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq17828
  have eq17847 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17844
  have eq17849 : False := by grind
  exact eq17849

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (k (M.op X1 X2) (M.op (M.op X0 X0) X1)) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X1)
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq45
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq45 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq126 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq77 sF0 y
       grind)
    | exact superpose eq77 eq126
    | (have j1 := eq77 (M.op x y) y
       grind)
    | exact resolve eq126 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (k x (k (M.op x y) y))) = (k (σ x) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq126 eq36
    | exact resolve eq36 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq143 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq156 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq77 (σ X0) sF2
       grind)
    | exact superpose eq77 eq40
    | (have j1 := eq77 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq202 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq77 (τ X0) X1
       grind)
    | exact superpose eq77 eq35
    | (have j1 := eq77 (τ X0) X1
       grind)
    | exact resolve eq35 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq410 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq293 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq293
    | (have j0 := eq293 X0 y
       grind)
    | exact resolve eq293 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq77 X0 (σ X1)
       grind)
    | exact superpose eq77 eq293
    | (have j1 := eq77 X0 (σ X1)
       grind)
    | exact resolve eq293 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq453 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) X1) X2) ∨ (k (M.op (M.op (M.op X0 X0) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X0) X1) X2) X0
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X0) X1) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq457 X0 X1 X2
       have j1 := eq77 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | (have r₁ := eq457 X1 X1 X2
       have r₂ := eq77 (M.op (M.op (M.op X1 X1) X1) X2) X1
       grind)
    | (have r₁ := eq457 X0 X1 (M.op (M.op X0 X0) X1)
       have r₂ := eq77 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq457 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq545 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq110
  have eq562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq561
    | exact resolve eq561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq565 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq562
       have r₂ := eq28
       grind)
    | exact resolve eq562 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq575 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq565 eq14
    | exact resolve eq14 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 (M.op (M.op (M.op X0 X0) X1) X2) X3
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq582 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq55 X1 X0 X2
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X1) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x)) (M.op (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x))) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x))) (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x)))) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq587 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y X0
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y) X0
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X1 (M.op X0 X2)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X2) (M.op X2 x)
       have i₂ := eq51 X0 X2 x
       grind)
    | (have i₁ := eq51 X0 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X3 (M.op X0 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq55 X1 X1 (M.op X1 X2)
       have i₂ := eq51 X1 X1 X2
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X3
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq14 X1 (M.op X1 X2) X2
       have i₂ := eq51 X1 X1 X2
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq53 (M.op X2 X2)
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq577 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq577
    | exact resolve eq577 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq835 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq872 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202 X0
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq202 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq202
    | exact resolve eq202 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 x) (M.op x y))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 (M.op X0 X0)
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq55
    | exact resolve eq55 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq888 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq53
    | exact resolve eq53 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq205 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq205
    | exact resolve eq205 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq957 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq914 eq51
    | exact resolve eq51 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op X0 (σ x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0 X1
       have i₂ := eq202 (M.op X0 sF2)
       grind)
    | exact superpose eq202 eq957
    | exact resolve eq957 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1055 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq588 X0
       have i₂ := eq202 x
       grind)
    | exact superpose eq202 eq588
    | exact resolve eq588 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq1120 : ∀ X0 : G, (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq589 X0
       have i₂ := eq202 sF2
       grind)
    | exact superpose eq202 eq589
    | exact resolve eq589 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq3205 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X0 X1 X2
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq453
    | exact resolve eq453 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq4319 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 X1 x (M.op X0 X1)
       have i₂ := eq51 (M.op X0 X1) (M.op X0 X1) (M.op X1 x)
       grind)
    | (have i₁ := eq604 X0 X0 X0 (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq51 eq604
    | exact resolve eq604 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4364 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4319 X0 X1
       have i₂ := eq202 (M.op X0 X1)
       grind)
    | exact superpose eq202 eq4319
    | exact resolve eq4319 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq6818 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq290
    | exact resolve eq290 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq6857 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq6818
    | (have j0 := eq6818 X0
       grind)
    | exact resolve eq6818 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq6818
  have eq7400 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq545 X0 X1 X2
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq545
    | exact resolve eq545 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq7683 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x x)) x) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq611 X0 (M.op x x) x
       have i₂ := eq7400 (M.op X0 (M.op x x)) x x
       grind)
    | exact superpose eq7400 eq611
    | exact resolve eq611 eq7400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7781 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 x) (M.op x y))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq546 X0 X1 X2
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq546
    | exact resolve eq546 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq10393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op X2 X3))) = (M.op (M.op X0 (M.op X1 X4)) (M.op X0 (M.op X1 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq625 (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0 X2
       have i₂ := eq604 X0 X1 X2 X3
       grind)
    | exact superpose eq604 eq625
    | exact resolve eq625 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10493 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 x)) (M.op (σ x) X1)) (M.op (σ (k X0 x)) (M.op (σ x) X1))) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq156 eq625
    | (have j1 := eq156 X0
       grind)
    | exact resolve eq625 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq11377 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq575 eq460
    | exact resolve eq460 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq12430 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq581 X0 X1 X2 X3
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq581
    | exact resolve eq581 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq13703 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11377 sF3
       grind)
    | exact superpose eq11377 eq87
    | exact resolve eq87 eq11377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq13781 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X1 (M.op X0 X2)) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq597 X0 X1 X2
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq597
    | exact resolve eq597 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq13782 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op x y)) = (M.op (M.op X1 (M.op X0 X2)) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13781 X0 X1 X2
       have i₂ := eq202 X1
       grind)
    | exact superpose eq202 eq13781
    | exact resolve eq13781 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13781
  have eq14585 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op x y)) x) = (M.op (M.op (M.op X0 (M.op x X1)) x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq13782 eq7400
    | exact resolve eq7400 eq13782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7400
  have eq21840 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op (M.op X0 X0) x) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq202 (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq202 eq584
    | exact resolve eq584 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq22491 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op X0 X0) (σ x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq202 (M.op (M.op X0 X0) sF2)
       grind)
    | exact superpose eq202 eq585
    | exact resolve eq585 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq22523 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) (σ x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq22491 (M.op X0 X0) X1
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq22491
    | exact resolve eq22491 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22558 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq22491 eq22491
    | exact resolve eq22491 eq22491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22627 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq22491 eq625
    | exact resolve eq625 eq22491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22804 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq3205 eq22627
    | exact resolve eq22627 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22627
  have eq22956 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq587 X0 X1 X2 X3
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq587
    | exact resolve eq587 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq22957 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22956 X0 X1 X2 X3
       have i₂ := eq202 (M.op X0 X1)
       grind)
    | exact superpose eq202 eq22956
    | exact resolve eq22956 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22956
  have eq24543 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq583 X0 X1 X2 X3
       have i₂ := eq202 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq202 eq583
    | exact resolve eq583 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq25127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X1) x) (M.op x y)) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24543 (M.op X0 X0) X1 X2 X3
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq24543
    | exact resolve eq24543 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25314 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) x) (M.op x y)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq604 X1 x x X0
       have i₂ := eq24543 (M.op X0 X0) X1 x (M.op x x)
       grind)
    | exact superpose eq24543 eq604
    | exact resolve eq604 eq24543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq25528 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X1) x) (M.op x y)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25314 X0 X1
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq25314
    | exact resolve eq25314 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25314
  have eq27158 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq565 eq13703
    | exact resolve eq13703 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq13703
  have eq27187 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by grind
  clear eq27158
  have eq27189 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq27187
    | exact resolve eq27187 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27187
  have eq27202 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11377 y
       have i₂ := eq27189
       grind)
    | exact superpose eq27189 eq11377
    | exact resolve eq11377 eq27189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11377 eq27189
  have eq27210 : x = (M.op y y) := by grind
  clear eq27202
  have eq28089 : y = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq53
    | exact resolve eq53 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28094 : (M.op x x) = (M.op (M.op y x) (M.op x y)) := by
    first
    | (have i₁ := eq202 y
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq202
    | exact resolve eq202 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28117 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op x x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq21840 y X0
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq21840
    | exact resolve eq21840 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21840
  have eq28121 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq14
    | exact resolve eq14 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28170 : ∀ X0 : G, x = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq28117
    | exact resolve eq28117 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28117
  have eq28178 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1055 eq28089
    | exact resolve eq28089 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28436 : (M.op (M.op x y) x) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq28170 eq1055
    | exact resolve eq1055 eq28170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28523 : y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq28089 eq28436
    | exact resolve eq28436 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28436
  have eq29649 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq582 X0 X1 X2 X3
       have i₂ := eq202 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq202 eq582
    | exact resolve eq582 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq30298 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x x) (M.op x y))) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op x y) (M.op x y)) X2)) x) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq1055 eq29649
    | exact resolve eq29649 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30509 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op (M.op (M.op (M.op X1 X1) (M.op (M.op x y) (M.op y X0))) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1055 eq29649
    | exact resolve eq29649 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30560 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq29649 eq29649
    | exact resolve eq29649 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30783 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1055 x
       have i₂ := eq29649 sF0 y x x
       grind)
    | exact superpose eq29649 eq1055
    | exact resolve eq1055 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30935 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq30783 X0
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq30783
    | exact resolve eq30783 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30783
  have eq31077 : ∀ X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op (M.op (M.op (M.op X1 X1) y) x) (M.op x y)) := by
    intro X1 X2
    first
    | exact superpose eq28178 eq30509
    | exact resolve eq30509 eq28178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28178 eq30509
  have eq31134 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op x y) (M.op x y)) X2)) x) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq28089 eq30298
    | exact resolve eq30298 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30298
  have eq31159 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28089 eq30935
    | exact resolve eq30935 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30935
  have eq31578 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq460 X0 y x
       have i₂ := eq28121 X0
       grind)
    | exact superpose eq28121 eq460
    | exact resolve eq460 eq28121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq31717 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq31578 (σ X0)
       grind)
    | exact superpose eq31578 eq10
    | exact resolve eq10 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31730 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq31578 x
       grind)
    | exact superpose eq31578 eq44
    | exact resolve eq44 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq31733 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq31578 y
       grind)
    | exact superpose eq31578 eq75
    | exact resolve eq75 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq31734 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq31578 sF0
       grind)
    | exact superpose eq31578 eq127
    | exact resolve eq127 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq31736 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq31578 sF2
       grind)
    | exact superpose eq31578 eq50
    | exact resolve eq50 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq31742 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq31736
       have i₂ := eq31578 x
       grind)
    | exact superpose eq31578 eq31736
    | exact resolve eq31736 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31736
  have eq31744 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq31734
       have i₂ := eq31578 sF1
       grind)
    | exact superpose eq31578 eq31734
    | exact resolve eq31734 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31734
  have eq31745 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq31733
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq31733
    | exact resolve eq31733 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31733
  have eq31746 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31730
       have i₂ := eq31578 sF2
       grind)
    | exact superpose eq31578 eq31730
    | exact resolve eq31730 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31730
  have eq31759 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31717 X0
       have i₂ := eq31578 X0
       grind)
    | exact superpose eq31578 eq31717
    | exact resolve eq31717 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31717
  have eq31774 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq31745
       have i₂ := eq31578 sF3
       grind)
    | exact superpose eq31578 eq31745
    | exact resolve eq31745 eq31578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31578 eq31745
  have eq31799 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq31774
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31774
    | exact resolve eq31774 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31774
  have eq31819 : ∀ X0 X1 X2 : G, y = (M.op (M.op x y) (M.op (M.op (M.op x X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq24543 eq31159
    | exact resolve eq31159 eq24543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31829 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq31159 eq3205
    | exact resolve eq3205 eq31159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31830 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq31159 eq12430
    | exact resolve eq12430 eq31159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31159
  have eq31912 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq28523 eq31830
    | exact resolve eq31830 eq28523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31830
  have eq31913 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq31829 X0
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq31829
    | exact resolve eq31829 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829
  have eq31942 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq31799 eq14
    | exact resolve eq14 eq31799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31946 : (σ y) = (M.op (M.op (σ x) x) (M.op x y)) := by
    first
    | exact superpose eq31799 eq53
    | exact resolve eq53 eq31799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31977 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ x)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq31799 eq22491
    | exact resolve eq22491 eq31799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22491
  have eq31985 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq31799 eq51
    | exact resolve eq51 eq31799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32041 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq31977
    | exact resolve eq31977 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31977
  have eq32054 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1120 eq31946
    | exact resolve eq31946 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32310 : (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq32041 eq1120
    | exact resolve eq1120 eq32041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32041
  have eq32396 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq31946 eq32310
    | exact resolve eq32310 eq31946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32310
  have eq32405 : ∀ X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op X1 (M.op x y)) := by
    intro X1 X2
    first
    | (have i₁ := eq31077 X1 X2
       have i₂ := eq28121 X1
       grind)
    | exact superpose eq28121 eq31077
    | exact resolve eq31077 eq28121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31077
  have eq32418 : (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32396 eq914
    | exact resolve eq914 eq32396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32524 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq13782 x X0 x
       have i₂ := eq32405 X0 x
       grind)
    | (have i₁ := eq13782 x x y
       have i₂ := eq32405 x x
       grind)
    | exact superpose eq32405 eq13782
    | (have j0 := eq13782 x X0 y
       grind)
    | exact resolve eq13782 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32640 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op x x) (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7781 x X0 x
       have i₂ := eq32405 (M.op X0 X0) x
       grind)
    | (have i₁ := eq7781 x x y
       have i₂ := eq32405 (M.op x x) x
       grind)
    | exact superpose eq32405 eq7781
    | (have j0 := eq7781 x X0 y
       grind)
    | exact resolve eq7781 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7781
  have eq32801 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) y) = X0 := by
    intro X0
    first
    | exact superpose eq28089 eq32640
    | exact resolve eq32640 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32640
  have eq32821 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq28089 eq32524
    | exact resolve eq32524 eq28089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32524
  have eq33366 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | exact superpose eq29649 eq31134
    | exact resolve eq31134 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29649 eq31134
  have eq34023 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq31913 x
       have i₂ := eq32405 (M.op sF0 sF0) x
       grind)
    | (have i₁ := eq31913 y
       have i₂ := eq32405 (M.op sF0 sF0) x
       grind)
    | exact superpose eq32405 eq31913
    | (have j0 := eq31913 y
       grind)
    | exact resolve eq31913 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31913
  have eq36439 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) y) x) := by
    first
    | exact superpose eq31942 eq28121
    | exact resolve eq28121 eq31942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28121
  have eq39122 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (M.op (σ x) x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1120 eq22558
    | exact resolve eq22558 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22558
  have eq39777 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq31946 eq39122
    | exact resolve eq39122 eq31946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31946 eq39122
  have eq39808 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq39777 (M.op (M.op X0 X0) sF4) x
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq39777
    | exact resolve eq39777 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40193 : (M.op (σ x) (σ x)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq31942 eq39808
    | exact resolve eq39808 eq31942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31942 eq39808
  have eq40373 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq22804 eq12430
    | exact resolve eq12430 eq22804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12430 eq22804
  have eq40463 : (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq39777 eq40373
    | exact resolve eq40373 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40373
  have eq41261 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30560 X0 y X1 y
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq30560
    | exact resolve eq30560 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41298 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq31799 eq30560
    | exact resolve eq30560 eq31799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31799
  have eq41544 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op x y) (M.op y X0))) = (M.op X1 (M.op (M.op x x) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1055 eq30560
    | exact resolve eq30560 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq41609 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = (M.op X1 (M.op (M.op (σ x) x) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1120 eq30560
    | exact resolve eq30560 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42774 : ∀ X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (M.op (σ x) x) X2)) := by
    intro X1 X2
    first
    | exact superpose eq39777 eq41609
    | exact resolve eq41609 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41609
  have eq42807 : ∀ X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op (M.op x x) X2)) := by
    intro X1 X2
    first
    | exact superpose eq33366 eq41544
    | exact resolve eq41544 eq33366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33366 eq41544
  have eq47922 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 y) (M.op (M.op (M.op x y) x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq31819 eq13782
    | exact resolve eq13782 eq31819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13782 eq31819
  have eq47933 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 y) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq28523 eq47922
    | exact resolve eq47922 eq28523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28523 eq47922
  have eq47961 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq47933 X0
       have i₂ := eq41261 (M.op X0 y) sF0
       grind)
    | exact superpose eq41261 eq47933
    | exact resolve eq47933 eq41261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47933
  have eq48196 : ∀ X0 : G, (M.op (M.op (M.op (σ x) x) x) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) y) := by
    intro X0
    first
    | exact superpose eq1120 eq32821
    | exact resolve eq32821 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32821
  have eq48401 : (M.op (M.op (M.op (σ x) x) x) (M.op x y)) = (M.op (σ y) y) := by
    first
    | exact superpose eq32054 eq48196
    | exact resolve eq48196 eq32054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48196
  have eq48832 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq32418 eq40463
    | exact resolve eq40463 eq32418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32418 eq40463
  have eq48841 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq48832 eq606
    | exact resolve eq606 eq48832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48852 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq48832 eq51
    | exact resolve eq51 eq48832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq48894 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) x) (M.op x y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq48832 eq3205
    | exact resolve eq3205 eq48832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48919 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) x) (M.op x y)) := by
    first
    | exact superpose eq22957 eq48894
    | exact resolve eq48894 eq22957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22957 eq48894
  have eq48960 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0
    first
    | exact superpose eq41298 eq48852
    | exact resolve eq48852 eq41298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48852
  have eq48968 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq41298 eq48841
    | exact resolve eq48841 eq41298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48841
  have eq48978 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) x) (M.op x y)) := by
    first
    | exact superpose eq48832 eq48919
    | exact resolve eq48919 eq48832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48832 eq48919
  have eq49016 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq39777 eq48960
    | exact resolve eq48960 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48960
  have eq49035 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq49016 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq49016
    | exact resolve eq49016 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq49016
  have eq54696 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y X0) (M.op X0 X1)) (M.op (M.op y x) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq606 y X0 X1 x
       have i₂ := eq47961 y
       grind)
    | exact superpose eq47961 eq606
    | exact resolve eq606 eq47961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq47961
  have eq54847 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y X0) (M.op X0 X1)) (M.op x x)) := by
    intro X0 X1
    first
    | exact superpose eq28094 eq54696
    | exact resolve eq54696 eq28094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28094 eq54696
  have eq54899 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y X0) (M.op X0 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq54847 X0 X1
       have i₂ := eq32405 (M.op (M.op y X0) (M.op X0 X1)) x
       grind)
    | exact superpose eq32405 eq54847
    | exact resolve eq54847 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54847
  have eq55030 : (M.op (σ x) x) = (M.op (M.op (σ y) y) (M.op (σ y) y)) := by
    first
    | exact superpose eq48401 eq3205
    | exact resolve eq3205 eq48401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48401
  have eq55154 : (M.op (σ x) x) = (M.op (M.op (σ y) y) (σ x)) := by
    first
    | exact superpose eq41298 eq55030
    | exact resolve eq55030 eq41298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41298 eq55030
  have eq55347 : (M.op (M.op (M.op (σ y) y) x) (M.op x y)) = (M.op (M.op (σ x) x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55154 eq914
    | exact resolve eq914 eq55154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq55154
  have eq55461 : (M.op (M.op (σ x) (σ x)) (M.op x y)) = (M.op (M.op (σ x) x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36439 eq55347
    | exact resolve eq55347 eq36439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36439 eq55347
  have eq57107 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ X0)) (σ (M.op X0 X0))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48968 (σ X0) (σ X0)
       have i₂ := eq31759 X0
       grind)
    | exact superpose eq31759 eq48968
    | exact resolve eq48968 eq31759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48968
  have eq59676 : (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) x) (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq40193 eq49035
    | exact resolve eq49035 eq40193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40193 eq49035
  have eq59877 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq48978 eq59676
    | exact resolve eq59676 eq48978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48978 eq59676
  have eq59918 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) x) (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq59877 eq24543
    | exact resolve eq24543 eq59877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24543 eq59877
  have eq60043 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq59918
    | exact resolve eq59918 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq59918
  have eq65389 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X0 X1)) = (M.op (M.op y (M.op (M.op x y) X2)) (M.op y (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54899 eq625
    | exact resolve eq625 eq54899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq54899
  have eq65442 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X0 X1)) = (M.op (M.op y (M.op (M.op x y) X2)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65389 X0 X1 X2
       have i₂ := eq41261 (M.op y (M.op sF0 X2)) (M.op sF0 X2)
       grind)
    | exact superpose eq41261 eq65389
    | exact resolve eq65389 eq41261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41261 eq65389
  have eq65785 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op y X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq28170 eq65442
    | exact resolve eq65442 eq28170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28170 eq65442
  have eq66806 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq137
    | exact resolve eq137 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq66809 : (M.op (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66806 eq16
    | exact resolve eq16 eq66806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66806
  have eq66875 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq143 eq66809
    | exact resolve eq66809 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq66809
  have eq69372 : (σ x) = (M.op (M.op (M.op (σ x) x) (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq55461 eq32801
    | exact resolve eq32801 eq55461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32801 eq55461
  have eq69678 : (k (σ x) (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) x) (M.op (σ x) (σ y))))) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq69372 eq835
    | exact resolve eq835 eq69372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69372
  have eq69719 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq60043 eq69678
    | exact resolve eq69678 eq60043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60043 eq69678
  have eq69766 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
    first
    | exact superpose eq42774 eq69719
    | exact resolve eq69719 eq42774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42774 eq69719
  have eq70306 : (k (M.op y y) (M.op (M.op x x) y)) = (M.op (M.op y y) (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq835 y y
       have i₂ := eq65785 y y
       grind)
    | exact superpose eq65785 eq835
    | exact resolve eq835 eq65785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq65785
  have eq70611 : (M.op (M.op y y) y) = (k (M.op y y) (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq70306
       have i₂ := eq42807 (M.op y y) y
       grind)
    | exact superpose eq42807 eq70306
    | exact resolve eq70306 eq42807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70306
  have eq70892 : (M.op x y) = (k x (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq70611
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq70611
    | exact resolve eq70611 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70611
  have eq70981 : (M.op x y) = (k x (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq70892
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70892
    | exact resolve eq70892 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq70892
  have eq90775 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op x x) (M.op x y))) = (M.op (M.op X0 (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq879 eq4364
    | exact resolve eq4364 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq91089 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op X0 (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90775 X0
       have i₂ := eq42807 (M.op X0 X0) sF0
       grind)
    | exact superpose eq42807 eq90775
    | exact resolve eq90775 eq42807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42807 eq90775
  have eq139988 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op X0 x)) y) = X0 := by
    intro X0
    first
    | exact superpose eq3205 eq91089
    | exact resolve eq91089 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91089
  have eq140895 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op X0 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139988 X0
       have i₂ := eq30560 (M.op X0 x) X0 X1 x
       grind)
    | (have i₁ := eq139988 X0
       have i₂ := eq30560 (M.op X0 x) X0 x X1
       grind)
    | exact superpose eq30560 eq139988
    | exact resolve eq139988 eq30560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30560 eq139988
  have eq144924 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7683 X0
       have i₂ := eq32405 X0 x
       grind)
    | exact superpose eq32405 eq7683
    | exact resolve eq7683 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7683
  have eq145068 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq888 eq144924
    | exact resolve eq144924 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq144924
  have eq170541 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1) x) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1120 eq25528
    | exact resolve eq25528 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120 eq25528
  have eq171050 : ∀ X1 : G, (σ x) = (M.op (M.op (M.op (M.op (σ y) X1) x) (M.op x y)) X1) := by
    intro X1
    first
    | exact superpose eq32054 eq170541
    | exact resolve eq170541 eq32054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32054 eq170541
  have eq171400 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op X0 X1)) x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ y) X0) x) (M.op x y)) (M.op (M.op (M.op (σ y) X0) x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq171050 eq611
    | exact resolve eq611 eq171050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq171050
  have eq171619 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (M.op X0 X1)) x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq3205 eq171400
    | exact resolve eq171400 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205 eq171400
  have eq198408 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq31759 X1
       grind)
    | exact superpose eq31759 eq417
    | (have j0 := eq417 X0 X1
       grind)
    | exact resolve eq417 eq31759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq198510 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (σ (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq198408 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq198408
    | (have j0 := eq198408 X0 y
       grind)
    | exact resolve eq198408 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198408
  have eq198702 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op X0 (σ y))) ∨ (σ (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq198510 X0
       have i₂ := eq410 X0
       grind)
    | exact superpose eq410 eq198510
    | (have j0 := eq198510 X0
       grind)
    | exact resolve eq198510 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq198510
  have eq198765 : ∀ X0 : G, (σ x) = X0 ∨ (τ (k X0 (σ y))) = (τ (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq198702 X0
       have i₂ := eq27210
       grind)
    | exact superpose eq27210 eq198702
    | (have j0 := eq198702 X0
       grind)
    | exact resolve eq198702 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27210 eq198702
  have eq198796 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op X0 (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq198765 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq198765
    | (have j0 := eq198765 X0
       grind)
    | exact resolve eq198765 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198765
  have eq202331 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (σ y)) = (M.op (M.op (M.op X0 (σ x)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq39777 eq960
    | exact resolve eq960 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq205752 : ∀ X0 : G, (k X0 (σ y)) = (σ (τ (M.op X0 (σ y)))) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq198796 eq15
    | (have j1 := eq198796 X0
       grind)
    | exact resolve eq15 eq198796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198796
  have eq205867 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq205752 X0
       have i₂ := eq15 (M.op X0 sF3)
       grind)
    | exact superpose eq15 eq205752
    | (have j0 := eq205752 X0
       grind)
    | exact resolve eq205752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205752
  have eq274278 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ y) X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq171619 eq4364
    | exact resolve eq4364 eq171619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364 eq171619
  have eq299866 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) x) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14585 X0 x
       have i₂ := eq32405 X0 x
       grind)
    | (have i₁ := eq14585 x y
       have i₂ := eq32405 x x
       grind)
    | exact superpose eq32405 eq14585
    | (have j0 := eq14585 X0 y
       grind)
    | exact resolve eq14585 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14585 eq32405
  have eq602741 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) x) (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq202331 eq22523
    | exact resolve eq22523 eq202331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22523
  have eq602742 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op x y)) x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq299866 eq602741
    | exact resolve eq602741 eq299866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602741
  have eq602743 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op x y)) x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39777 eq602742
    | exact resolve eq602742 eq39777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39777 eq602742
  have eq1040122 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op (M.op X1 x) (M.op x y))) = (M.op (M.op X0 (M.op X1 X4)) (M.op X0 (M.op X1 X4))) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq10393 X0 X1 x x X4
       have i₂ := eq872 X1 x x
       grind)
    | (have i₁ := eq10393 X0 X0 x y X4
       have i₂ := eq872 X0 X1 x
       grind)
    | exact superpose eq872 eq10393
    | (have j0 := eq10393 X0 X1 x y X4
       grind)
    | exact resolve eq10393 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq10393
  have eq1714167 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (k X0 x)) (σ (k X0 x))) (M.op (M.op (σ x) x) (M.op x y))) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10493 X0 x
       have i₂ := eq1040122 (σ (k X0 x)) sF2 x
       grind)
    | exact superpose eq1040122 eq10493
    | (have j0 := eq10493 X0 x
       grind)
    | exact resolve eq10493 eq1040122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10493 eq1040122
  have eq1714168 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op (M.op (M.op (σ (k X0 x)) x) (M.op x y)) (σ x)) x) (M.op x y)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1714167 X0
       have i₂ := eq25127 (σ (k X0 x)) sF2 x sF0
       grind)
    | exact superpose eq25127 eq1714167
    | (have j0 := eq1714167 X0
       grind)
    | exact resolve eq1714167 eq25127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25127 eq1714167
  have eq1714169 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op (M.op (M.op (σ (k X0 x)) x) (M.op x y)) x) (M.op x y)) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq202331 eq1714168
    | (have j0 := eq1714168 X0
       grind)
    | exact resolve eq1714168 eq202331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202331 eq1714168
  have eq1714170 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op (M.op (M.op (σ (k X0 x)) x) x) (M.op x y)) x) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq299866 eq1714169
    | (have j0 := eq1714169 X0
       grind)
    | exact resolve eq1714169 eq299866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299866 eq1714169
  have eq1714228 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (σ (M.op (M.op x y) x)) x) x) (M.op x y)) x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq6857 eq1714170
    | (have j0 := eq1714170 (M.op x y)
       have j1 := eq6857 x
       grind)
    | exact resolve eq1714170 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857 eq1714170
  have eq1714758 : (σ (M.op x y)) = (M.op (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq602743 eq1714228
    | exact resolve eq1714228 eq602743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602743 eq1714228
  have eq1714914 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1714758
       have i₂ := eq31759 (M.op sF0 x)
       grind)
    | exact superpose eq31759 eq1714758
    | exact resolve eq1714758 eq31759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31759 eq1714758
  have eq1715020 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1714914
       have i₂ := eq145068 sF0
       grind)
    | exact superpose eq145068 eq1714914
    | exact resolve eq1714914 eq145068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145068 eq1714914
  have eq1715080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq34023 eq1715020
    | exact resolve eq1715020 eq34023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34023 eq1715020
  have eq1715102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1715080
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1715080
    | exact resolve eq1715080 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715080
  have eq1715119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq1715102
    | exact resolve eq1715102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1715102
  have eq1715133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq1715119
    | exact resolve eq1715119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715119
  have eq1715140 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1715133
       have r₂ := eq28
       grind)
    | exact resolve eq1715133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715133
  have eq1715145 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq1715140
    | exact resolve eq1715140 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715140
  have eq1715154 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1715145 eq31742
    | exact resolve eq31742 eq1715145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31742 eq1715145
  have eq1716117 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31 eq1715154
    | exact resolve eq1715154 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1715154
  have eq1716118 : (M.op x y) = (M.op x x) := by grind
  clear eq1716117
  have eq1716318 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq28089
       have i₂ := eq1716118
       grind)
    | exact superpose eq1716118 eq28089
    | exact resolve eq28089 eq1716118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28089
  have eq1716320 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31746
       have i₂ := eq1716118
       grind)
    | exact superpose eq1716118 eq31746
    | exact resolve eq31746 eq1716118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31746
  have eq1716328 : (M.op x y) = (k x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq70981
       have i₂ := eq1716118
       grind)
    | exact superpose eq1716118 eq70981
    | exact resolve eq70981 eq1716118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70981
  have eq1716681 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq57107 x
       have i₂ := eq1716118
       grind)
    | exact superpose eq1716118 eq57107
    | exact resolve eq57107 eq1716118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57107
  have eq1716965 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq140895 x x
       have i₂ := eq1716118
       grind)
    | exact superpose eq1716118 eq140895
    | exact resolve eq140895 eq1716118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140895 eq1716118
  have eq1717131 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq31912 eq1716965
    | exact resolve eq1716965 eq31912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31912 eq1716965
  have eq1717278 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq21 eq1716681
    | exact resolve eq1716681 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716681
  have eq1717489 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq1716320
    | exact resolve eq1716320 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716320
  have eq1717594 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq1717278
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1717278
    | exact resolve eq1717278 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1717278
  have eq1717726 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq32396 eq1717594
    | exact resolve eq1717594 eq32396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32396 eq1717594
  have eq1717805 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1716318 eq31744
    | exact resolve eq31744 eq1716318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31744 eq1716318
  have eq1718772 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1717805
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1717805
    | exact resolve eq1717805 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1717805
  have eq1719270 : x ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1717131 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq1717131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717131
  have eq1719613 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq1719270
       have r₂ := eq66875
       grind)
    | exact resolve eq1719270 eq66875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66875 eq1719270
  have eq1728419 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq1717489 eq69766
    | exact resolve eq69766 eq1717489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69766
  have eq1755884 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq274278 eq1717726
    | exact resolve eq1717726 eq274278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274278 eq1717726
  have eq1761909 : (k (σ x) (k (σ (M.op x y)) (σ y))) = (σ (k x (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1719613 eq140
    | exact resolve eq140 eq1719613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1719613
  have eq1762025 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq1716328 eq1761909
    | exact resolve eq1761909 eq1716328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716328 eq1761909
  have eq1762077 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq21 eq1762025
    | exact resolve eq1762025 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1762025
  have eq1820517 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq205867 eq1762077
    | (have j1 := eq205867 (σ (M.op x y))
       grind)
    | exact resolve eq1762077 eq205867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205867 eq1762077
  have eq1820553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1728419 eq1820517
    | exact resolve eq1820517 eq1728419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728419 eq1820517
  have eq1820560 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1820553
       have r₂ := eq28
       grind)
    | exact resolve eq1820553 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820553
  have eq1821186 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1820560 eq1717489
    | exact resolve eq1717489 eq1820560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820560
  have eq1821209 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1718772 eq1821186
    | exact resolve eq1821186 eq1718772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718772 eq1821186
  have eq1822166 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq1821209 eq31985
    | exact resolve eq31985 eq1821209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31985 eq1821209
  have eq1823206 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1755884 eq1822166
    | exact resolve eq1822166 eq1755884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755884 eq1822166
  have eq1823572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1717489 eq1823206
    | exact resolve eq1823206 eq1717489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717489 eq1823206
  have eq1823798 : False := by grind
  exact eq1823798

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (k (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op (M.op X0 X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X1)
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq75
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq75 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq38
  have eq209 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k (M.op X0 X0) X0) x) (M.op x y)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq352 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) X1) X2) ∨ (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X0) X1) X2) X0
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq13
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1 X2
    grind
  have eq513 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 (M.op (M.op (M.op X0 X0) X1) X2) X3
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq55 X1 X0 X2
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x))) (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x)))) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y) X0
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X3 (M.op X0 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq55 X1 X1 (M.op X1 X2)
       have i₂ := eq51 X1 X1 X2
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) (M.op X1 X2)) ∨ (M.op (M.op X0 X1) (M.op X1 X2)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq13 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq13
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 (M.op X0 X0))
       have r₂ := eq51 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq509 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq509
    | (have j0 := eq509 X0 x x
       grind)
    | exact resolve eq509 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq559 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq508
    | exact resolve eq508 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq628 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq627
    | exact resolve eq627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq631 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq628
       have r₂ := eq28
       grind)
    | exact resolve eq628 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq643 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq656 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq631 eq14
    | exact resolve eq14 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1969 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq522 X0
       have i₂ := eq209 sF2
       grind)
    | exact superpose eq209 eq522
    | exact resolve eq522 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq14689 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq513 X0 X1 X2 X3
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq513
    | exact resolve eq513 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq22705 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq656 eq352
    | exact resolve eq352 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq656
  have eq22715 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22705 X0
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq22705 X0
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq22705 (M.op x x)
       have r₂ := eq69 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq22705 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22705
  have eq22802 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq50
       have i₂ := eq22715 sF2
       grind)
    | exact superpose eq22715 eq50
    | exact resolve eq50 eq22715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq24415 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq631 eq22802
    | exact resolve eq22802 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq22802
  have eq24442 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by grind
  clear eq24415
  have eq24444 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq24442
    | exact resolve eq24442 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24442
  have eq24449 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22715 x
       have i₂ := eq24444
       grind)
    | exact superpose eq24444 eq22715
    | exact resolve eq22715 eq24444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22715 eq24444
  have eq24457 : y = (M.op x x) := by grind
  clear eq24449
  have eq24478 : ∀ X0 X1 : G, x = (M.op (M.op y X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq14
    | exact resolve eq14 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24481 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X1 x
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq52
    | exact resolve eq52 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq24482 : x = (M.op (M.op y x) (M.op x y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq53
    | exact resolve eq53 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq24484 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op y X1)) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0 X1
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq55
    | exact resolve eq55 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq24494 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq209 x
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq209
    | exact resolve eq209 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24516 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq14
    | exact resolve eq14 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25345 : ∀ X0 X1 X2 : G, (M.op (M.op y y) (M.op (M.op x y) X0)) = (M.op (M.op y y) (M.op (M.op (M.op (M.op y y) (M.op (M.op x y) X0)) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq24494 eq543
    | exact resolve eq543 eq24494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24494
  have eq25371 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (M.op (M.op y y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq25345 X0 x x
       have i₂ := eq14689 y (M.op sF0 X0) x x
       grind)
    | exact superpose eq14689 eq25345
    | exact resolve eq25345 eq14689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14689 eq25345
  have eq25373 : ∀ X0 : G, x = (M.op (M.op y y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq24482 eq25371
    | exact resolve eq25371 eq24482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24482 eq25371
  have eq25541 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq24478 (M.op y X0) (M.op X0 x)
       have i₂ := eq24478 X0 x
       grind)
    | exact superpose eq24478 eq24478
    | exact resolve eq24478 eq24478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24478
  have eq26724 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq25373 eq14
    | exact resolve eq14 eq25373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25373
  have eq27198 : ∀ X0 X1 : G, (M.op (M.op (M.op y (M.op y X0)) (M.op y (M.op y X0))) (M.op (M.op y (M.op y X0)) (M.op y (M.op y X0)))) = (M.op x (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op y (M.op y X0)) x X1
       have i₂ := eq25541 X0
       grind)
    | exact superpose eq25541 eq51
    | exact resolve eq51 eq25541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27246 : ∀ X0 X1 : G, (M.op (M.op (M.op y (M.op y X0)) x) (M.op x y)) = (M.op x (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27198 X0 X1
       have i₂ := eq209 (M.op y (M.op y X0))
       grind)
    | exact superpose eq209 eq27198
    | exact resolve eq27198 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27198
  have eq27249 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op x (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq27246 x X1
       have i₂ := eq25541 x
       grind)
    | exact superpose eq25541 eq27246
    | exact resolve eq27246 eq25541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25541 eq27246
  have eq30097 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq26724 eq27249
    | exact resolve eq27249 eq26724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26724 eq27249
  have eq30177 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq30097
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30097
    | exact resolve eq30097 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30097
  have eq30195 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq30177 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq30177
       grind)
    | exact resolve eq13 eq30177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30177
  have eq30248 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq30195
  have eq30538 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq30248 eq132
    | exact resolve eq132 eq30248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30248
  have eq30544 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq30538
    | exact resolve eq30538 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30538
  have eq30551 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30544
       have i₂ := eq69 sF1 sF2
       grind)
    | exact superpose eq69 eq30544
    | (have j1 := eq69 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq30544 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30926 : (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ x)) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30551 eq210
    | exact resolve eq210 eq30551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq30940 : (σ x) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30551 eq558
    | exact resolve eq558 eq30551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq30956 : (σ x) = (M.op (M.op (σ (M.op x y)) x) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30551 eq24516
    | exact resolve eq24516 eq30551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30551
  have eq31018 : (σ x) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq30940
  have eq31022 : (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ x)) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq30926
  have eq31037 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30544 eq31018
    | exact resolve eq31018 eq30544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31018
  have eq31042 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30544 eq31022
    | exact resolve eq31022 eq30544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31022
  have eq32510 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op y X1)) (M.op (M.op X0 X0) (M.op y X1))) (M.op (M.op (M.op X0 X0) (M.op y X1)) (M.op (M.op X0 X0) (M.op y X1)))) = (M.op X0 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op y X1)) x X2
       have i₂ := eq24484 X0 X1
       grind)
    | exact superpose eq24484 eq51
    | exact resolve eq51 eq24484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32587 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op y X1)) x) (M.op x y)) = (M.op X0 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32510 X0 X1 X2
       have i₂ := eq209 (M.op (M.op X0 X0) (M.op y X1))
       grind)
    | exact superpose eq209 eq32510
    | exact resolve eq32510 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32510
  have eq32610 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq32587 X0 x X2
       have i₂ := eq24484 X0 x
       grind)
    | exact superpose eq24484 eq32587
    | exact resolve eq32587 eq24484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24484 eq32587
  have eq32620 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq32610 X0 (M.op (M.op y x) x)
       have i₂ := eq24481 x x
       grind)
    | exact superpose eq24481 eq32610
    | exact resolve eq32610 eq24481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24481 eq32610
  have eq33260 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) y) := by
    intro X0
    first
    | exact superpose eq1969 eq32620
    | exact resolve eq32620 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq35993 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq518 X0 X1 X2 X3
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq518
    | exact resolve eq518 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq35994 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 x) y) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq32620 eq35993
    | exact resolve eq35993 eq32620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35993
  have eq35995 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) (M.op x y)) = (M.op (M.op (M.op X0 x) y) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35994 X0 X1 X2 X3
       have i₂ := eq209 (M.op X0 X1)
       grind)
    | exact superpose eq209 eq35994
    | exact resolve eq35994 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35994
  have eq35996 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) y) = (M.op (M.op (M.op X0 x) y) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq32620 eq35995
    | exact resolve eq35995 eq32620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35995
  have eq38923 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op X0 X0) (σ x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq209 (M.op (M.op X0 X0) sF2)
       grind)
    | exact superpose eq209 eq520
    | exact resolve eq520 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq38924 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op X0 X0) (σ x)) x) y) := by
    intro X0 X1
    first
    | exact superpose eq32620 eq38923
    | exact resolve eq38923 eq32620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38923
  have eq39143 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) x) y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq38924 (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       have i₂ := eq537 sF2 sF2 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq537 eq38924
    | exact resolve eq38924 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq39220 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) y) (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) y)) = X0 := by
    intro X0
    first
    | exact superpose eq38924 eq559
    | exact resolve eq559 eq38924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38924
  have eq39499 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x))) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq39220 X0
       have i₂ := eq35996 (M.op (M.op (M.op X0 sF4) (M.op X0 sF4)) sF2) (M.op (M.op (M.op X0 sF4) (M.op X0 sF4)) sF2) x y
       grind)
    | exact superpose eq35996 eq39220
    | exact resolve eq39220 eq35996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39220
  have eq39535 : ∀ X0 : G, (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ x)) x) y) := by
    intro X0
    first
    | (have i₁ := eq39143 X0
       have i₂ := eq209 sF2
       grind)
    | exact superpose eq209 eq39143
    | exact resolve eq39143 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39143
  have eq39581 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq39499 X0
       have i₂ := eq24516 (M.op (M.op (M.op X0 sF4) (M.op X0 sF4)) sF2)
       grind)
    | exact superpose eq24516 eq39499
    | exact resolve eq39499 eq24516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39499
  have eq39609 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq39535 X0
       have i₂ := eq24516 sF2
       grind)
    | exact superpose eq24516 eq39535
    | exact resolve eq39535 eq24516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39535
  have eq39627 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq32620 eq39609
    | exact resolve eq39609 eq32620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39609
  have eq41692 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq39581 eq643
    | exact resolve eq643 eq39581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq41694 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq39581 eq14
    | exact resolve eq14 eq39581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42206 : (σ x) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq41694 eq39581
    | exact resolve eq39581 eq41694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39581
  have eq43115 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) x) y) (M.op (M.op (σ x) x) y)) (M.op (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq39627 eq543
    | exact resolve eq543 eq39627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq43168 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) x) y) (M.op (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43115 X0 X1 X2 X3
       have i₂ := eq35996 sF2 sF2 x y
       grind)
    | exact superpose eq35996 eq43115
    | exact resolve eq43115 eq35996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43115
  have eq43197 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1))) x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq43168 X0 X1 x x
       have i₂ := eq35996 (M.op sF2 sF2) (M.op sF2 (M.op (M.op sF4 X0) X1)) x x
       grind)
    | exact superpose eq35996 eq43168
    | exact resolve eq43168 eq35996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43168
  have eq43212 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq43197 X0 X1
       have i₂ := eq51 sF2 sF2 (M.op (M.op sF4 X0) X1)
       grind)
    | exact superpose eq51 eq43197
    | exact resolve eq43197 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq43197
  have eq43218 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43212 X0 X1
       have i₂ := eq24516 (M.op sF2 sF2)
       grind)
    | exact superpose eq24516 eq43212
    | exact resolve eq43212 eq24516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43212
  have eq78234 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq514 X0 X1 X2 X3
       have i₂ := eq209 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq209 eq514
    | exact resolve eq514 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq514
  have eq78235 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq32620 eq78234
    | exact resolve eq78234 eq32620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78234
  have eq78912 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) y) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) y)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq559 X0 X1 x
       have i₂ := eq78235 (M.op X0 X1) X1 X2 x
       grind)
    | exact superpose eq78235 eq559
    | exact resolve eq559 eq78235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq78235
  have eq79470 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2))) x) y) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78912 X0 X1 X2
       have i₂ := eq35996 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x y
       grind)
    | exact superpose eq35996 eq78912
    | exact resolve eq78912 eq35996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35996 eq78912
  have eq79765 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79470 X0 X1 X2
       have i₂ := eq24516 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq24516 eq79470
    | exact resolve eq79470 eq24516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24516 eq79470
  have eq93173 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq33260 eq39627
    | exact resolve eq39627 eq33260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33260 eq39627
  have eq98117 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) ≠ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq93173 eq548
    | exact resolve eq548 eq93173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98193 : ∀ X0 X1 X2 : G, (σ x) ≠ (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) ∨ (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq93173 eq98117
    | (have j0 := eq98117 X0 X1 X2
       grind)
    | exact resolve eq98117 eq93173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98117
  have eq98254 : ∀ X0 X1 X2 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq43218 eq98193
    | (have j0 := eq98193 X0 X1 X2
       grind)
    | exact resolve eq98193 eq43218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98193
  have eq98279 : ∀ X1 X2 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq93173 eq98254
    | exact resolve eq98254 eq93173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93173 eq98254
  have eq98288 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43218 eq98279
    | exact resolve eq98279 eq43218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43218 eq98279
  have eq98294 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq69 (σ x) (σ x)
       grind)
    | (have r₁ := eq98288
       have r₂ := eq69 (σ x) (σ x)
       grind)
    | exact resolve eq98288 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98288
  have eq132471 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) x) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq32620 eq31042
    | exact resolve eq31042 eq32620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31042 eq32620
  have eq138444 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq132471 eq30956
    | exact resolve eq30956 eq132471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30956 eq132471
  have eq138560 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq138444
  have eq138607 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq138560 eq41694
    | exact resolve eq41694 eq138560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139182 : (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq138607 eq42206
    | exact resolve eq42206 eq138607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42206
  have eq149352 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq138560 eq139182
    | exact resolve eq139182 eq138560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138560 eq139182
  have eq149466 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq149352
  have eq149553 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq138607 eq149466
    | exact resolve eq149466 eq138607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138607 eq149466
  have eq149654 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq149553
  have eq149758 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq149654 eq54
    | exact resolve eq54 eq149654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq149654
  have eq179619 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X1 X2)) ≠ X0 ∨ (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X1 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq548 (M.op (M.op X1 X1) (M.op X1 X1)) X1 X2
       have i₂ := eq79765 X1 X1 (M.op X1 X1)
       grind)
    | exact superpose eq79765 eq548
    | exact resolve eq548 eq79765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq79765
  have eq179996 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X1 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179619 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq179619
    | (have j0 := eq179619 X0 X1 X2
       grind)
    | exact resolve eq179619 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179619
  have eq180555 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq179996 X0 x x
       have i₂ := eq14 (M.op X0 X0) x x
       grind)
    | exact superpose eq14 eq179996
    | (have j0 := eq179996 X0 x x
       grind)
    | exact resolve eq179996 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179996
  have eq180825 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq180555 X0
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq180555 X0
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq180555 (M.op x x)
       have r₂ := eq69 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq180555 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180555
  have eq181090 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq180825 x
       grind)
    | exact superpose eq180825 eq44
    | exact resolve eq44 eq180825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180825
  have eq181137 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq181090
       have i₂ := eq24457
       grind)
    | exact superpose eq24457 eq181090
    | exact resolve eq181090 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24457 eq181090
  have eq181178 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98294 eq181137
    | exact resolve eq181137 eq98294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181137
  have eq181206 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq181178
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq181178
    | exact resolve eq181178 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq181178
  have eq181252 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq181206 eq41694
    | exact resolve eq41694 eq181206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41694
  have eq182268 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq181252 eq41692
    | exact resolve eq41692 eq181252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41692
  have eq182278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq181252 eq149758
    | exact resolve eq149758 eq181252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149758
  have eq182418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq182278
    | exact resolve eq182278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182278
  have eq182426 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq182268
    | exact resolve eq182268 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq182268
  have eq182563 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq182418
       have r₂ := eq28
       grind)
    | exact resolve eq182418 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182418
  have eq182638 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq182563 eq29
    | exact resolve eq29 eq182563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq182949 : x = (M.op x y) := by
    first
    | exact superpose eq31 eq182638
    | exact resolve eq182638 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq182638
  have eq182986 : (σ (k x x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq182949 eq132
    | exact resolve eq132 eq182949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq182949
  have eq183164 : (σ (M.op x y)) = (σ (k x x)) := by
    first
    | exact superpose eq30544 eq182986
    | exact resolve eq182986 eq30544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30544 eq182986
  have eq183200 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq183164
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq183164
    | exact resolve eq183164 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq183164
  have eq183220 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98294 eq183200
    | exact resolve eq183200 eq98294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98294 eq183200
  have eq183231 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq181206 eq183220
    | exact resolve eq183220 eq181206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181206 eq183220
  have eq185029 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq182563 eq182426
    | exact resolve eq182426 eq182563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182426
  have eq185036 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq185029 eq69
    | (have j0 := eq69 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq69 eq185029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq185029
  have eq185037 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq181252 eq185036
    | exact resolve eq185036 eq181252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181252 eq185036
  have eq185041 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq183231 eq185037
    | exact resolve eq185037 eq183231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183231 eq185037
  have eq185042 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq185041
  have eq185052 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq185042 eq31037
    | exact resolve eq31037 eq185042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31037
  have eq185522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq182563 eq185052
    | exact resolve eq185052 eq182563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185052
  have eq185714 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq185522
       have r₂ := eq28
       grind)
    | exact resolve eq185522 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185522
  have eq185852 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq182563 eq185714
    | exact resolve eq185714 eq182563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182563 eq185714
  have eq185958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq185042 eq185852
    | exact resolve eq185852 eq185042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185042 eq185852
  have eq186030 : False := by grind
  exact eq186030
