import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pyx_Equation3385 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3385 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 X2
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq25 X1 X3 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq25 X0 X0 X0
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 X0 X1 X2 X3
       have i₂ := eq101 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq95 X0 X1 X2 X0
       have i₂ := eq101 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq95
    | exact resolve eq95 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 X0 X1 X2 X3
       have i₂ := eq101 X2 X3 X1
       grind)
    | (have i₁ := eq109 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq101 eq109
    | exact resolve eq109 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X2 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 (M.op X1 X2) X3 (M.op X2 X0)
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq101
    | exact resolve eq101 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op X0 X1) X2
       have i₂ := eq101 X1 X2 X0
       grind)
    | exact superpose eq101 eq25
    | exact resolve eq25 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq101 eq9
    | exact resolve eq9 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X2 (M.op X0 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq128 X0 x X2 X3
       have i₂ := eq111 x X2 X0 X3
       grind)
    | exact superpose eq111 eq128
    | exact resolve eq128 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq136 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125 X0 X1 X2 X3
       have i₂ := eq101 (M.op X1 X2) (M.op X3 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq125 X0 X1 X2 X0
       have i₂ := eq101 X0 (M.op X0 X1) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq101 eq125
    | exact resolve eq125 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq142 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq117 X0 X1 X2 X3
       have i₂ := eq101 X0 (M.op (M.op X1 X2) X3) X2
       grind)
    | (have i₁ := eq117 X0 X1 X2 X1
       have i₂ := eq101 (M.op X1 X2) X1 (M.op X2 X0)
       grind)
    | exact superpose eq101 eq117
    | exact resolve eq117 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq144 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq136 X0 x X2 X3
       have i₂ := eq102 X0 x X3 X2
       grind)
    | exact superpose eq102 eq136
    | exact resolve eq136 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq146 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq142 X0 X1 X2 X3
       have i₂ := eq101 X2 X3 X1
       grind)
    | (have i₁ := eq142 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq101 eq142
    | exact resolve eq142 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq148 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146 X0 X1 X2 X3
       have i₂ := eq101 X1 X3 X0
       grind)
    | (have i₁ := eq146 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq101 eq146
    | exact resolve eq146 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq165 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op (M.op X4 X0) (M.op (M.op X1 X4) X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X4 X0) (M.op X1 X4) X2 X3
       have i₂ := eq25 X1 X4 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op X4 (M.op X5 X1)) (M.op (M.op X0 (M.op X4 X5)) X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X4 (M.op X5 X1)) (M.op X0 (M.op X4 X5)) X2 X3
       have i₂ := eq24 X4 X5 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X1)) (M.op (M.op X0 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq101 (M.op X0 (M.op X2 X3)) X4 (M.op X2 (M.op X3 X1))
       have i₂ := eq24 X2 X3 X0 X1
       grind)
    | exact superpose eq24 eq101
    | exact resolve eq101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq24 X2 X3 X0 X1
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq24 X3 X4 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq182 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq182 X0 X1 X0 X3 X4
       have i₂ := eq101 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq101 eq182
    | exact resolve eq182 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq189 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq181 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq181 X0 X1 X2 X3 X0
       have i₂ := eq101 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq181
    | exact resolve eq181 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq191 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4) X2
       grind)
    | (have i₁ := eq179 X0 X1 X2 X3 X1
       have i₂ := eq101 (M.op X0 (M.op X2 X3)) X1 (M.op X2 (M.op X3 X1))
       grind)
    | exact superpose eq101 eq179
    | exact resolve eq179 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq203 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op X4 (M.op X5 X1)) (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq167 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)) (M.op X4 (M.op X5 X1))
       grind)
    | (have i₁ := eq167 X0 X1 X0 X3 X4 X5
       have i₂ := eq101 X0 (M.op X0 X1) (M.op (M.op X4 (M.op X5 X1)) (M.op (M.op X0 (M.op X4 X5)) X3))
       grind)
    | exact superpose eq101 eq167
    | exact resolve eq167 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq205 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X4 X0) (M.op (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq165 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1)) (M.op X4 X0)
       grind)
    | (have i₁ := eq165 X0 X1 X0 X3 X4
       have i₂ := eq101 X0 (M.op X0 X1) (M.op (M.op X4 X0) (M.op (M.op X1 X4) X3))
       grind)
    | exact superpose eq101 eq165
    | exact resolve eq165 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq221 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X3 X4) (M.op X2 X1)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq188 x X1 X2 X3 X4
       have i₂ := eq148 (M.op X3 X4) X2 x X1
       grind)
    | exact superpose eq148 eq188
    | exact resolve eq188 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq222 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq189 X0 x X2 X3 X4
       have i₂ := eq111 x X4 X3 X2
       grind)
    | exact superpose eq111 eq189
    | exact resolve eq189 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq224 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op X3 (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq191 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 (M.op (M.op X0 (M.op X2 X3)) X4) X3
       grind)
    | (have i₁ := eq191 X0 X1 X2 X3 X1
       have i₂ := eq101 (M.op X0 (M.op X2 X3)) X1 (M.op X3 X1)
       grind)
    | exact superpose eq101 eq191
    | exact resolve eq191 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq236 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op X5 X1) (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq203 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op X5 X1) (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq203 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)) (M.op X4 (M.op X5 X1))
       grind)
    | exact superpose eq101 eq203
    | exact resolve eq203 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq238 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op X0 (M.op (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq205 X0 X1 X2 X3 X4
       have i₂ := eq101 X0 (M.op (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq205 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1)) (M.op X4 X0)
       grind)
    | exact superpose eq101 eq205
    | exact resolve eq205 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq253 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X3 (M.op X4 (M.op X2 X1))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq221 X1 X2 X3 X4
       have i₂ := eq101 X4 (M.op X2 X1) X3
       grind)
    | (have i₁ := eq221 X1 x X3 X4
       have i₂ := eq101 x X1 (M.op X3 X4)
       grind)
    | exact superpose eq101 eq221
    | exact resolve eq221 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq254 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq222 X0 X2 X3 X4
       have i₂ := eq101 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq222 X0 X2 X3 (M.op X0 x)
       have i₂ := eq101 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq101 eq222
    | exact resolve eq222 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq256 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 (M.op (M.op X2 X3) X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq224 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq224 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq101 eq224
    | exact resolve eq224 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq265 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X1 (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq236 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 X1 (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1))) X5
       grind)
    | (have i₁ := eq236 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)) (M.op X5 X1)
       grind)
    | exact superpose eq101 eq236
    | exact resolve eq236 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq267 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op (M.op X1 X4) X3) (M.op X2 X1))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq238 x X1 X2 X3 X4
       have i₂ := eq148 (M.op (M.op X1 X4) X3) X2 x X1
       grind)
    | exact superpose eq148 eq238
    | exact resolve eq238 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq238
  have eq274 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq254 X0 X4 X3 X2
       have i₂ := eq101 X3 X2 X4
       grind)
    | (have i₁ := eq254 X0 X2 X3 (M.op X0 x)
       have i₂ := eq101 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq101 eq254
    | exact resolve eq254 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq276 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 (M.op X2 (M.op X3 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq256 X0 X1 X2 X3 X4
       have i₂ := eq101 X3 X4 X2
       grind)
    | (have i₁ := eq256 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq101 eq256
    | exact resolve eq256 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq280 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X0 X2)))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq265 X0 x X2 X3 X4 X5
       have i₂ := eq111 x (M.op (M.op X0 (M.op X4 X5)) X3) X0 X2
       grind)
    | exact superpose eq111 eq265
    | exact resolve eq265 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq282 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op X1 X4) (M.op X3 (M.op X2 X1)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq267 X1 X2 X3 X4
       have i₂ := eq101 X3 (M.op X2 X1) (M.op X1 X4)
       grind)
    | (have i₁ := eq267 X1 x X3 X4
       have i₂ := eq101 x X1 (M.op (M.op X1 X4) X3)
       grind)
    | exact superpose eq101 eq267
    | exact resolve eq267 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq287 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 (M.op X2 (M.op X3 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq276 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 X4 X0
       grind)
    | (have i₁ := eq276 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq101 eq276
    | exact resolve eq276 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq291 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op (M.op X0 (M.op X4 X5)) (M.op X3 (M.op X0 X2))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq280 X0 X2 X3 X4 X5
       have i₂ := eq101 X3 (M.op X0 X2) (M.op X0 (M.op X4 X5))
       grind)
    | (have i₁ := eq280 X0 x X3 X4 X5
       have i₂ := eq101 X0 x (M.op (M.op X0 (M.op X4 X5)) X3)
       grind)
    | exact superpose eq101 eq280
    | exact resolve eq280 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq292 : ∀ X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op X3 (M.op X4 X2))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq282 x X2 X3 X4
       have i₂ := eq102 X2 x X3 X4
       grind)
    | exact superpose eq102 eq282
    | exact resolve eq282 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq296 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X0 (M.op (M.op X0 (M.op X4 X5)) (M.op X3 X2))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq291 X0 X2 X3 X4 X5
       have i₂ := eq253 X2 X0 (M.op X0 (M.op X4 X5)) X3
       grind)
    | (have i₁ := eq291 X4 x X3 X4 X5
       have i₂ := eq253 x (M.op X4 (M.op X4 X5)) X3 X4
       grind)
    | exact superpose eq253 eq291
    | exact resolve eq291 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq298 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X0 (M.op X0 (M.op (M.op X4 X5) (M.op X3 X2)))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq296 X0 X2 X3 X4 X5
       have i₂ := eq101 (M.op X4 X5) (M.op X3 X2) X0
       grind)
    | (have i₁ := eq296 X0 x X0 X4 X5
       have i₂ := eq101 X0 x (M.op X0 (M.op X4 X5))
       grind)
    | exact superpose eq101 eq296
    | exact resolve eq296 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq299 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X0 (M.op X0 (M.op X4 (M.op X5 (M.op X3 X2))))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq298 X0 X2 X3 X4 X5
       have i₂ := eq101 X5 (M.op X3 X2) X4
       grind)
    | (have i₁ := eq298 X0 x X0 X4 X5
       have i₂ := eq101 X0 x (M.op X4 X5)
       grind)
    | exact superpose eq101 eq298
    | exact resolve eq298 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq300 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X0 (M.op X3 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq299 X0 X2 X3 x x
       have i₂ := eq287 X0 X0 x x (M.op X3 X2)
       grind)
    | exact superpose eq287 eq299
    | exact resolve eq299 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq299
  have eq315 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq316 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq315 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq315 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq315 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq321 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq316 (σ X0)
       grind)
    | exact superpose eq316 eq15
    | exact resolve eq15 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq316 (τ X0)
       grind)
    | exact superpose eq316 eq34
    | exact resolve eq34 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq326 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq323
    | exact resolve eq323 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq321
    | exact resolve eq321 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq321
  have eq479 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq292 X1 X0 X1
       grind)
    | exact superpose eq292 eq9
    | exact resolve eq9 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 X1 X2 (M.op X3 X0)
       have i₂ := eq292 X0 X1 X3
       grind)
    | exact superpose eq292 eq24
    | exact resolve eq24 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq482 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X2 X0)
       have i₂ := eq292 X0 X1 X2
       grind)
    | exact superpose eq292 eq9
    | exact resolve eq9 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 X0 X1 X2
       have i₂ := eq101 X0 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq482 X0 X1 X2
       have i₂ := eq101 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq101 eq482
    | exact resolve eq482 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq498 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq481 X0 X1 X2 X3
       have i₂ := eq101 X1 (M.op X2 (M.op X3 X1)) X0
       grind)
    | (have i₁ := eq481 X0 X1 X0 X3
       have i₂ := eq101 X0 (M.op X3 X1) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq481
    | exact resolve eq481 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq518 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X0 (M.op X2 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq498 X0 x X2 X3
       have i₂ := eq9 X2 X3 x
       grind)
    | exact superpose eq9 eq498
    | exact resolve eq498 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq606 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq607 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq606 X0 X1
       grind)
    | (have r₁ := eq606 X0 X1
       have r₂ := eq479 X0 X1
       grind)
    | (have r₁ := eq606 X1 X0
       have r₂ := eq479 X0 X1
       grind)
    | exact resolve eq606 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq914 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X2 (M.op X1 X0)
       have i₂ := eq300 X2 X0 X1
       grind)
    | exact superpose eq300 eq9
    | exact resolve eq9 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq937 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq914 X0 X1 X2
       have i₂ := eq518 X1 (M.op X1 X0) X0
       grind)
    | (have i₁ := eq914 X2 x X2
       have i₂ := eq518 (M.op x X2) X2 x
       grind)
    | exact superpose eq518 eq914
    | exact resolve eq914 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq914
  have eq965 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq937 X0 X1 X2
       have i₂ := eq479 (M.op X1 X0) X0
       grind)
    | (have i₁ := eq937 X0 X1 X2
       have i₂ := eq479 X0 (M.op X1 X0)
       grind)
    | exact superpose eq479 eq937
    | exact resolve eq937 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq983 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq965 X2 x X0
       have i₂ := eq134 x X2 X2
       grind)
    | (have i₁ := eq965 X0 X2 X2
       have i₂ := eq134 X0 X2 (M.op X0 (M.op X2 X0))
       grind)
    | exact superpose eq134 eq965
    | exact resolve eq965 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq965
  have eq1341 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1
       have i₂ := eq983 (σ X1) X0
       grind)
    | (have i₁ := eq328 X1
       have i₂ := eq983 X0 (σ X1)
       grind)
    | exact superpose eq983 eq328
    | exact resolve eq328 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 X1
       have i₂ := eq983 (τ X1) X0
       grind)
    | (have i₁ := eq326 X1
       have i₂ := eq983 X0 (τ X1)
       grind)
    | exact superpose eq983 eq326
    | exact resolve eq326 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq1564 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (τ X2)) = (τ (k (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X1 X1) X2
       have i₂ := eq1341 X0 X1
       grind)
    | exact superpose eq1341 eq31
    | exact resolve eq31 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1567 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X1) X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X1 X1) X2
       have i₂ := eq1341 X0 X1
       grind)
    | exact superpose eq1341 eq15
    | exact resolve eq15 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1569 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X1) X2)) = (M.op (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1567 X0 X1 X2
       have i₂ := eq104 X0 (σ X2)
       grind)
    | exact superpose eq104 eq1567
    | exact resolve eq1567 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1570 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (τ X2)) = (τ (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1564 X0 X1 X2
       have i₂ := eq104 X0 X2
       grind)
    | exact superpose eq104 eq1564
    | exact resolve eq1564 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1584 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X1) X2)) = (M.op X0 (M.op X0 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1569 X0 X1 X2
       have i₂ := eq101 X0 (σ X2) X0
       grind)
    | exact superpose eq101 eq1569
    | exact resolve eq1569 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1585 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (τ X2)) = (τ (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1570 X0 X1 X2
       have i₂ := eq101 X0 X2 X0
       grind)
    | (have i₁ := eq1570 X0 X1 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq101 eq1570
    | exact resolve eq1570 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1592 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ X2))) = (σ (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1584 X0 X1 X2
       have i₂ := eq104 X1 X2
       grind)
    | exact superpose eq104 eq1584
    | exact resolve eq1584 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1593 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X2))) = (M.op (M.op X1 X1) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1585 X0 X1 X2
       have i₂ := eq104 X1 (τ X2)
       grind)
    | exact superpose eq104 eq1585
    | exact resolve eq1585 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1585
  have eq1599 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ X2))) = (σ (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1592 X0 X1 X2
       have i₂ := eq101 X1 X2 X1
       grind)
    | (have i₁ := eq1592 X0 X1 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq101 eq1592
    | exact resolve eq1592 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1600 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X2))) = (M.op X1 (M.op X1 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1593 X0 X1 X2
       have i₂ := eq101 X1 (τ X2) X1
       grind)
    | exact superpose eq101 eq1593
    | exact resolve eq1593 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq3458 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq607 X0 (τ X1)
       grind)
    | exact superpose eq607 eq19
    | (have j1 := eq607 X0 (τ X1)
       grind)
    | exact resolve eq19 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3501 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X1 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1342 X1 X2
       have i₂ := eq607 X2 X0
       grind)
    | (have i₁ := eq1342 X0 X1
       have i₂ := eq607 X0 (M.op X1 X1)
       grind)
    | exact superpose eq607 eq1342
    | (have j1 := eq607 X2 X0
       grind)
    | exact resolve eq1342 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq1342
  have eq5319 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4)) = (M.op (M.op X0 (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq101 (M.op X0 (M.op X2 X3)) X4 (M.op X3 X1)
       have i₂ := eq102 X2 X3 X0 X1
       grind)
    | exact superpose eq102 eq101
    | exact resolve eq101 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq5394 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4)) = (M.op X0 (M.op (M.op X1 X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5319 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X1 X2) X4 X0
       grind)
    | (have i₁ := eq5319 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq101 eq5319
    | exact resolve eq5319 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq5556 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4)) = (M.op X0 (M.op X1 (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5394 X0 X1 X2 X3 X4
       have i₂ := eq101 X2 X4 X1
       grind)
    | (have i₁ := eq5394 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq101 eq5394
    | exact resolve eq5394 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5394
  have eq5659 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4))) = (M.op X0 (M.op X1 (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5556 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 (M.op (M.op X0 (M.op X2 X3)) X4) X3
       grind)
    | (have i₁ := eq5556 X0 X1 X2 X3 X1
       have i₂ := eq101 (M.op X0 (M.op X2 X3)) X1 (M.op X3 X1)
       grind)
    | exact superpose eq101 eq5556
    | exact resolve eq5556 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556
  have eq5725 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X1 (M.op X0 (M.op (M.op X2 X3) X4)))) = (M.op X0 (M.op X1 (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5659 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq5659 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq101 eq5659
    | exact resolve eq5659 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5770 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X1 (M.op X0 (M.op X2 (M.op X3 X4))))) = (M.op X0 (M.op X1 (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5725 X0 X1 X2 X3 X4
       have i₂ := eq101 X3 X4 X2
       grind)
    | (have i₁ := eq5725 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq101 eq5725
    | exact resolve eq5725 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq5725
  have eq6131 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X2 (M.op X1 X3)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op X2 (M.op X1 X3))
       have i₂ := eq111 X3 X0 X1 X2
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq6180 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op X1 (M.op (M.op X2 (M.op X1 X3)) (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6131 X0 X1 X2 X3
       have i₂ := eq253 X2 X1 (M.op X2 (M.op X1 X3)) X0
       grind)
    | (have i₁ := eq6131 X3 x X1 X3
       have i₂ := eq253 X1 (M.op X1 (M.op x X3)) X3 x
       grind)
    | exact superpose eq253 eq6131
    | exact resolve eq6131 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq6131
  have eq6281 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op X1 (M.op X2 (M.op X0 (M.op X2 (M.op X1 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6180 X0 X1 X2 X3
       have i₂ := eq274 X1 X2 X0 (M.op X2 (M.op X1 X3))
       grind)
    | (have i₁ := eq6180 X0 X1 X2 X3
       have i₂ := eq274 X1 (M.op X2 (M.op X1 X3)) X0 X2
       grind)
    | exact superpose eq274 eq6180
    | exact resolve eq6180 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq6180
  have eq6348 : ∀ X0 X2 X3 : G, (M.op X3 X0) = (M.op X0 (M.op X2 (M.op X2 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6281 X0 x X2 X3
       have i₂ := eq5770 X0 X2 X2 x X3
       grind)
    | exact superpose eq5770 eq6281
    | exact resolve eq6281 eq5770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770 eq6281
  have eq301298 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ (M.op X1 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1599 X2 X3 (M.op X1 (M.op X3 X0))
       have i₂ := eq292 X0 X1 X3
       grind)
    | exact superpose eq292 eq1599
    | exact resolve eq1599 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq301416 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (M.op X2 (σ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1599 X2 X0 (M.op X0 X1)
       have i₂ := eq497 X0 X1 X0
       grind)
    | exact superpose eq497 eq1599
    | exact resolve eq1599 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq301607 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 X1))
       have i₂ := eq1599 X0 X2 X1
       grind)
    | exact superpose eq1599 eq10
    | exact resolve eq10 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq301805 : ∀ X0 X1 X3 : G, (σ (M.op X3 (M.op X0 X1))) = (σ (M.op X1 (M.op X3 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq301298 X0 X1 x X3
       have i₂ := eq301416 X1 (M.op X3 X0) x
       grind)
    | exact superpose eq301416 eq301298
    | exact resolve eq301298 eq301416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301298 eq301416
  have eq307018 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1600 X1 X2 (M.op X1 X0)
       have i₂ := eq6348 X1 X1 X0
       grind)
    | exact superpose eq6348 eq1600
    | exact resolve eq1600 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq6348
  have eq366848 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3501 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq3501 eq15
    | (have j1 := eq3501 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq3501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501
  have eq366866 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq366848 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq366848
    | (have j0 := eq366848 X0 X1 X2
       grind)
    | exact resolve eq366848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366848
  have eq463034 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (τ (M.op X0 (M.op (σ X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301607 (M.op (σ X1) X0) X1 X2
       have i₂ := eq25 (M.op (σ X1) X0) (σ X1) X0
       grind)
    | exact superpose eq25 eq301607
    | exact resolve eq301607 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq301607
  have eq491938 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (τ (M.op X1 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144 (τ (M.op X1 X0)) X2 X2
       have i₂ := eq307018 X0 X1 X2
       grind)
    | exact superpose eq307018 eq144
    | exact resolve eq144 eq307018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq307018
  have eq509332 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3458 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3458
    | exact resolve eq3458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq509384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq509332 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq509332
    | (have j0 := eq509332 X0 X1
       grind)
    | exact resolve eq509332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509332
  have eq647704 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X2))) = (σ (τ (M.op X0 (M.op (σ X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301805 X2 X1 X2
       have i₂ := eq463034 X0 X1 X2
       grind)
    | exact superpose eq463034 eq301805
    | exact resolve eq301805 eq463034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301805 eq463034
  have eq648004 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X2))) = (M.op X0 (M.op (σ X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647704 X0 X1 X2
       have i₂ := eq11 (M.op X0 (M.op (σ X1) X0))
       grind)
    | exact superpose eq11 eq647704
    | exact resolve eq647704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647704
  have eq658954 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op (τ (M.op X0 X1)) (τ (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq328 X2
       have i₂ := eq491938 X1 X0 (σ X2)
       grind)
    | exact superpose eq491938 eq328
    | exact resolve eq328 eq491938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq491938
  have eq746506 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq983 X1 X2
       have i₂ := eq509384 X0 X2
       grind)
    | (have i₁ := eq983 X0 X2
       have i₂ := eq509384 (M.op X2 X2) X1
       grind)
    | exact superpose eq509384 eq983
    | (have j1 := eq509384 X0 X2
       grind)
    | exact resolve eq983 eq509384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq509384
  have eq1172221 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq366866 x y X0
       grind)
    | exact superpose eq366866 eq16
    | (have j1 := eq366866 X0 y X0
       grind)
    | exact resolve eq16 eq366866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366866
  have eq1172298 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq1172221 X0
       have j1 := eq746506 y X0 x
       grind)
    | (have r₁ := eq1172221 X0
       have r₂ := eq746506 y x x
       grind)
    | exact resolve eq1172221 eq746506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746506 eq1172221
  have eq1175339 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq648004 (σ X0) X0 X1
       have i₂ := eq1172298 (σ X0)
       grind)
    | exact superpose eq1172298 eq648004
    | exact resolve eq648004 eq1172298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648004
  have eq1175510 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq658954 x x X0
       have i₂ := eq1172298 (τ (M.op x x))
       grind)
    | exact superpose eq1172298 eq658954
    | exact resolve eq658954 eq1172298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658954
  have eq1175597 : y = (σ y) := by
    first
    | (have i₁ := eq1175510 x
       have i₂ := eq1172298 x
       grind)
    | exact superpose eq1172298 eq1175510
    | exact resolve eq1175510 eq1172298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175510
  have eq1175757 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op y (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1175339 X0 X1
       have i₂ := eq479 (σ X0) y
       grind)
    | (have i₁ := eq1175339 X0 X1
       have i₂ := eq479 y (σ X0)
       grind)
    | exact superpose eq479 eq1175339
    | exact resolve eq1175339 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175339
  have eq1178223 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1175757 X0 x
       have i₂ := eq1172298 x
       grind)
    | exact superpose eq1172298 eq1175757
    | exact resolve eq1175757 eq1172298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172298 eq1175757
  have eq1182625 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1175597
       grind)
    | exact superpose eq1175597 eq16
    | exact resolve eq16 eq1175597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175597
  have eq1182931 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq1182625
       have i₂ := eq479 (σ x) y
       grind)
    | (have i₁ := eq1182625
       have i₂ := eq479 y (σ x)
       grind)
    | exact superpose eq479 eq1182625
    | exact resolve eq1182625 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq1182625
  have eq1183042 : False := by grind
  exact eq1183042

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pxy_Equation3385 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3385 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X1 X0)) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq74 (k X1 X0) X1
       grind)
    | (have r₁ := eq66 X0 X0
       have r₂ := eq74 X0 (k X0 X0)
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq66 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq74
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X0 X1) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 X2
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq25 X1 X3 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq25 X0 X0 X0
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 X0 X1 X2 X3
       have i₂ := eq101 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq95 X0 X1 X2 X0
       have i₂ := eq101 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq95
    | exact resolve eq95 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X0 (M.op X1 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X2 X3
       have i₂ := eq101 X1 (M.op X3 X2) X0
       grind)
    | (have i₁ := eq92 X0 X1 X1 X0
       have i₂ := eq101 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq101 eq92
    | exact resolve eq92 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 X0 X1 X2 X3
       have i₂ := eq101 X2 X3 X1
       grind)
    | (have i₁ := eq109 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq101 eq109
    | exact resolve eq109 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 X2))) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X0 X1 X2 X3
       have i₂ := eq101 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq110 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq101 eq110
    | exact resolve eq110 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 X2))) = (M.op X0 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112 X0 X1 X2 X3
       have i₂ := eq101 X2 X3 X1
       grind)
    | (have i₁ := eq112 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq101 eq112
    | exact resolve eq112 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X2 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 (M.op X1 X2) X3 (M.op X2 X0)
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq101
    | exact resolve eq101 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq101 eq9
    | exact resolve eq9 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X2 (M.op X0 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq128 X0 x X2 X3
       have i₂ := eq111 x X2 X0 X3
       grind)
    | exact superpose eq111 eq128
    | exact resolve eq128 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq143 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq117 X0 X1 X2 X3
       have i₂ := eq101 X0 (M.op (M.op X1 X2) X3) X2
       grind)
    | (have i₁ := eq117 X0 X1 X2 X1
       have i₂ := eq101 (M.op X1 X2) X1 (M.op X2 X0)
       grind)
    | exact superpose eq101 eq117
    | exact resolve eq117 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq149 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq143 X0 X1 X2 X3
       have i₂ := eq101 X2 X3 X1
       grind)
    | (have i₁ := eq143 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq101 eq143
    | exact resolve eq143 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq153 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq149 X0 X1 X2 X3
       have i₂ := eq101 X1 X3 X0
       grind)
    | (have i₁ := eq149 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq101 eq149
    | exact resolve eq149 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq172 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op (M.op X4 X0) (M.op (M.op X1 X4) X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X4 X0) (M.op X1 X4) X2 X3
       have i₂ := eq25 X1 X4 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op X4 (M.op X5 X1)) (M.op (M.op X0 (M.op X4 X5)) X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X4 (M.op X5 X1)) (M.op X0 (M.op X4 X5)) X2 X3
       have i₂ := eq24 X4 X5 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X1)) (M.op (M.op X0 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq101 (M.op X0 (M.op X2 X3)) X4 (M.op X2 (M.op X3 X1))
       have i₂ := eq24 X2 X3 X0 X1
       grind)
    | exact superpose eq24 eq101
    | exact resolve eq101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq24 X2 X3 X0 X1
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq24 X3 X4 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 (M.op X0 X0)) X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 X0 X0 X0
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq189 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq189 X0 X1 X0 X3 X4
       have i₂ := eq101 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq101 eq189
    | exact resolve eq189 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq197 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq188 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq188 X0 X1 X2 X3 X0
       have i₂ := eq101 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq188
    | exact resolve eq188 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq199 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq186 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X3 X1) (M.op (M.op X0 (M.op X2 X3)) X4) X2
       grind)
    | (have i₁ := eq186 X0 X1 X2 X3 X1
       have i₂ := eq101 (M.op X0 (M.op X2 X3)) X1 (M.op X2 (M.op X3 X1))
       grind)
    | exact superpose eq101 eq186
    | exact resolve eq186 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq211 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op X4 (M.op X5 X1)) (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq174 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)) (M.op X4 (M.op X5 X1))
       grind)
    | (have i₁ := eq174 X0 X1 X0 X3 X4 X5
       have i₂ := eq101 X0 (M.op X0 X1) (M.op (M.op X4 (M.op X5 X1)) (M.op (M.op X0 (M.op X4 X5)) X3))
       grind)
    | exact superpose eq101 eq174
    | exact resolve eq174 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq213 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X4 X0) (M.op (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq172 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1)) (M.op X4 X0)
       grind)
    | (have i₁ := eq172 X0 X1 X0 X3 X4
       have i₂ := eq101 X0 (M.op X0 X1) (M.op (M.op X4 X0) (M.op (M.op X1 X4) X3))
       grind)
    | exact superpose eq101 eq172
    | exact resolve eq172 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq230 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X3 X4) (M.op X2 X1)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq196 x X1 X2 X3 X4
       have i₂ := eq153 (M.op X3 X4) X2 x X1
       grind)
    | exact superpose eq153 eq196
    | exact resolve eq196 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq231 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq197 X0 x X2 X3 X4
       have i₂ := eq111 x X4 X3 X2
       grind)
    | exact superpose eq111 eq197
    | exact resolve eq197 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq233 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op X3 (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq199 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 (M.op (M.op X0 (M.op X2 X3)) X4) X3
       grind)
    | (have i₁ := eq199 X0 X1 X2 X3 X1
       have i₂ := eq101 (M.op X0 (M.op X2 X3)) X1 (M.op X3 X1)
       grind)
    | exact superpose eq101 eq199
    | exact resolve eq199 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq245 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op X5 X1) (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq211 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op X5 X1) (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq211 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)) (M.op X4 (M.op X5 X1))
       grind)
    | exact superpose eq101 eq211
    | exact resolve eq211 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq247 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op X0 (M.op (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq213 X0 X1 X2 X3 X4
       have i₂ := eq101 X0 (M.op (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq213 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op (M.op X1 X4) X3) (M.op X2 (M.op X0 X1)) (M.op X4 X0)
       grind)
    | exact superpose eq101 eq213
    | exact resolve eq213 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq263 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X3 (M.op X4 (M.op X2 X1))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq230 X1 X2 X3 X4
       have i₂ := eq101 X4 (M.op X2 X1) X3
       grind)
    | (have i₁ := eq230 X1 x X3 X4
       have i₂ := eq101 x X1 (M.op X3 X4)
       grind)
    | exact superpose eq101 eq230
    | exact resolve eq230 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq264 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq231 X0 X2 X3 X4
       have i₂ := eq101 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq231 X0 X2 X3 (M.op X0 x)
       have i₂ := eq101 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq101 eq231
    | exact resolve eq231 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq266 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 (M.op (M.op X2 X3) X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq233 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq233 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq101 eq233
    | exact resolve eq233 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq275 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X1 (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq245 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 X1 (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1))) X5
       grind)
    | (have i₁ := eq245 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X2 (M.op X0 X1)) (M.op X5 X1)
       grind)
    | exact superpose eq101 eq245
    | exact resolve eq245 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq277 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op (M.op X1 X4) X3) (M.op X2 X1))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq247 x X1 X2 X3 X4
       have i₂ := eq153 (M.op (M.op X1 X4) X3) X2 x X1
       grind)
    | exact superpose eq153 eq247
    | exact resolve eq247 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq284 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq264 X0 X4 X3 X2
       have i₂ := eq101 X3 X2 X4
       grind)
    | (have i₁ := eq264 X0 X2 X3 (M.op X0 x)
       have i₂ := eq101 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq101 eq264
    | exact resolve eq264 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq286 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 (M.op X2 (M.op X3 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq266 X0 X1 X2 X3 X4
       have i₂ := eq101 X3 X4 X2
       grind)
    | (have i₁ := eq266 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq101 eq266
    | exact resolve eq266 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq292 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op (M.op (M.op X0 (M.op X4 X5)) X3) (M.op X0 X2)))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq275 X0 x X2 X3 X4 X5
       have i₂ := eq111 x (M.op (M.op X0 (M.op X4 X5)) X3) X0 X2
       grind)
    | exact superpose eq111 eq275
    | exact resolve eq275 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq294 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op X1 X4) (M.op X3 (M.op X2 X1)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq277 X1 X2 X3 X4
       have i₂ := eq101 X3 (M.op X2 X1) (M.op X1 X4)
       grind)
    | (have i₁ := eq277 X1 x X3 X4
       have i₂ := eq101 x X1 (M.op (M.op X1 X4) X3)
       grind)
    | exact superpose eq101 eq277
    | exact resolve eq277 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq300 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 (M.op X2 (M.op X3 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq286 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 X4 X0
       grind)
    | (have i₁ := eq286 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq101 eq286
    | exact resolve eq286 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq306 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op (M.op X0 (M.op X4 X5)) (M.op X3 (M.op X0 X2))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq292 X0 X2 X3 X4 X5
       have i₂ := eq101 X3 (M.op X0 X2) (M.op X0 (M.op X4 X5))
       grind)
    | (have i₁ := eq292 X0 x X3 X4 X5
       have i₂ := eq101 X0 x (M.op (M.op X0 (M.op X4 X5)) X3)
       grind)
    | exact superpose eq101 eq292
    | exact resolve eq292 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq307 : ∀ X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op X3 (M.op X4 X2))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq294 x X2 X3 X4
       have i₂ := eq102 X2 x X3 X4
       grind)
    | exact superpose eq102 eq294
    | exact resolve eq294 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq315 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X0 (M.op (M.op X0 (M.op X4 X5)) (M.op X3 X2))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq306 X0 X2 X3 X4 X5
       have i₂ := eq263 X2 X0 (M.op X0 (M.op X4 X5)) X3
       grind)
    | (have i₁ := eq306 X4 x X3 X4 X5
       have i₂ := eq263 x (M.op X4 (M.op X4 X5)) X3 X4
       grind)
    | exact superpose eq263 eq306
    | exact resolve eq306 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq318 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X0 (M.op X0 (M.op (M.op X4 X5) (M.op X3 X2)))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq315 X0 X2 X3 X4 X5
       have i₂ := eq101 (M.op X4 X5) (M.op X3 X2) X0
       grind)
    | (have i₁ := eq315 X0 x X0 X4 X5
       have i₂ := eq101 X0 x (M.op X0 (M.op X4 X5))
       grind)
    | exact superpose eq101 eq315
    | exact resolve eq315 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq319 : ∀ X0 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X4 (M.op X5 (M.op X0 (M.op X0 (M.op X4 (M.op X5 (M.op X3 X2))))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq318 X0 X2 X3 X4 X5
       have i₂ := eq101 X5 (M.op X3 X2) X4
       grind)
    | (have i₁ := eq318 X0 x X0 X4 X5
       have i₂ := eq101 X0 x (M.op X4 X5)
       grind)
    | exact superpose eq101 eq318
    | exact resolve eq318 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq320 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X0 (M.op X3 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq319 X0 X2 X3 x x
       have i₂ := eq300 X0 X0 x x (M.op X3 X2)
       grind)
    | exact superpose eq300 eq319
    | exact resolve eq319 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq319
  have eq333 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq334 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq333 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq333 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq333 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq334 (σ X0)
       grind)
    | exact superpose eq334 eq15
    | exact resolve eq15 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq339
    | exact resolve eq339 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq339
  have eq371 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (σ X0) X1
       have i₂ := eq346 X0
       grind)
    | exact superpose eq346 eq104
    | exact resolve eq104 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X0 X0 X0
       have i₂ := eq77 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq77 eq24
    | (have j1 := eq77 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq24 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq451 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op X0 (M.op (M.op X0 X0) X1)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 X1
       have i₂ := eq101 (M.op X0 X0) X1 X0
       grind)
    | (have i₁ := eq445 X0 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq101 eq445
    | (have j0 := eq445 X0 X1
       grind)
    | exact resolve eq445 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq467 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq101 X0 X1 X0
       grind)
    | (have i₁ := eq451 X0 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq101 eq451
    | (have j0 := eq451 X0 X1
       grind)
    | exact resolve eq451 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq478 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq135 X0 X0 X1
       grind)
    | (have i₁ := eq467 x X1
       have i₂ := eq135 X0 x (M.op x (M.op x X1))
       grind)
    | exact superpose eq135 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq505 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq307 X1 X0 X1
       grind)
    | exact superpose eq307 eq9
    | exact resolve eq9 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 X1 X2 (M.op X3 X0)
       have i₂ := eq307 X0 X1 X3
       grind)
    | exact superpose eq307 eq24
    | exact resolve eq24 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X2 X0)
       have i₂ := eq307 X0 X1 X2
       grind)
    | exact superpose eq307 eq9
    | exact resolve eq9 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 X0 X1 X2
       have i₂ := eq101 X0 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq508 X0 X1 X2
       have i₂ := eq101 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq101 eq508
    | exact resolve eq508 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq524 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq507 X0 X1 X2 X3
       have i₂ := eq101 X1 (M.op X2 (M.op X3 X1)) X0
       grind)
    | (have i₁ := eq507 X0 X1 X0 X3
       have i₂ := eq101 X0 (M.op X3 X1) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq507
    | exact resolve eq507 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq545 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X0 (M.op X2 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq524 X0 x X2 X3
       have i₂ := eq9 X2 X3 x
       grind)
    | exact superpose eq9 eq524
    | exact resolve eq524 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq951 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X2 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 X3 X2 (M.op X1 X0)
       have i₂ := eq320 X3 X0 X1
       grind)
    | exact superpose eq320 eq24
    | exact resolve eq24 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X2 (M.op X1 X0)
       have i₂ := eq320 X2 X0 X1
       grind)
    | exact superpose eq320 eq9
    | exact resolve eq9 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq952 X0 X1 X2
       have i₂ := eq545 X1 (M.op X1 X0) X0
       grind)
    | (have i₁ := eq952 X2 x X2
       have i₂ := eq545 (M.op x X2) X2 x
       grind)
    | exact superpose eq545 eq952
    | exact resolve eq952 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq976 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq951 X0 X1 X2 X3
       have i₂ := eq101 X1 (M.op X2 (M.op X3 X3)) X0
       grind)
    | (have i₁ := eq951 X0 X1 X0 X3
       have i₂ := eq101 X0 (M.op X3 X3) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq951
    | exact resolve eq951 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1003 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq975 X0 X1 X2
       have i₂ := eq505 (M.op X1 X0) X0
       grind)
    | (have i₁ := eq975 X0 X1 X2
       have i₂ := eq505 X0 (M.op X1 X0)
       grind)
    | exact superpose eq505 eq975
    | exact resolve eq975 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq975
  have eq1021 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq1003 X2 x X0
       have i₂ := eq135 x X2 X2
       grind)
    | (have i₁ := eq1003 X0 X2 X2
       have i₂ := eq135 X0 X2 (M.op X0 (M.op X2 X0))
       grind)
    | exact superpose eq135 eq1003
    | exact resolve eq1003 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1082 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op X2 (M.op X1 X0))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X0 X2 X3
       have i₂ := eq64 X3 X0 X1
       grind)
    | exact superpose eq64 eq24
    | (have j1 := eq64 X3 X1 X1
       grind)
    | exact resolve eq24 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1165 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X0))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1082 X0 X1 X2 X3
       have i₂ := eq263 X0 X1 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq1082 X1 x X3 X3
       have i₂ := eq263 X1 (M.op X1 x) X3 x
       grind)
    | exact superpose eq263 eq1082
    | (have j0 := eq1082 X0 X1 X2 X3
       grind)
    | exact resolve eq1082 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1208 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X1 (M.op X0 (M.op X2 (M.op X0 X1)))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1165 X0 X1 X2 X3
       have i₂ := eq284 X1 X0 X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq1165 X0 X1 X2 X3
       have i₂ := eq284 X1 (M.op X0 X1) X2 X0
       grind)
    | exact superpose eq284 eq1165
    | (have j0 := eq1165 X0 X1 X2 X3
       grind)
    | exact resolve eq1165 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1242 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X0 X2)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1208 X0 X1 X2 X3
       have i₂ := eq111 X1 X0 X0 X2
       grind)
    | exact superpose eq111 eq1208
    | (have j0 := eq1208 X0 X1 X2 X3
       grind)
    | exact resolve eq1208 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1388 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X1
       have i₂ := eq1021 (σ X1) X0
       grind)
    | (have i₁ := eq346 X1
       have i₂ := eq1021 X0 (σ X1)
       grind)
    | exact superpose eq1021 eq346
    | exact resolve eq346 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq1021
  have eq1601 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ (M.op X0 X0)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 X1 X1
       have i₂ := eq1388 X1 X0
       grind)
    | exact superpose eq1388 eq25
    | exact resolve eq25 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1388
  have eq5433 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X4 X3))) = (M.op X2 (M.op (M.op X3 (M.op X1 X0)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq102 X4 X3 X2 (M.op X3 (M.op X1 X0))
       have i₂ := eq320 X3 X0 X1
       grind)
    | exact superpose eq320 eq102
    | exact resolve eq102 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5465 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op X0 (M.op X1 X4)) X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq102 X4 (M.op X0 (M.op X1 X4)) X2 X3
       have i₂ := eq9 X0 X1 X4
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5493 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 X1))) = (M.op (M.op X2 X4) (M.op X3 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq102 (M.op X0 X1) X2 X3 X4
       have i₂ := eq101 X1 X2 X0
       grind)
    | exact superpose eq101 eq102
    | exact resolve eq102 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5562 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq307 X2 X0 (M.op X2 X1)
       have i₂ := eq102 (M.op X2 X1) X2 X0 X1
       grind)
    | exact superpose eq102 eq307
    | exact resolve eq307 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq5734 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 X1))) = (M.op X2 (M.op X4 (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5493 X0 X1 X2 X3 X4
       have i₂ := eq101 X4 (M.op X3 (M.op X0 (M.op X1 X2))) X2
       grind)
    | (have i₁ := eq5493 X0 X1 X2 X0 X4
       have i₂ := eq101 X0 (M.op X0 (M.op X1 X2)) (M.op X2 X4)
       grind)
    | exact superpose eq101 eq5493
    | exact resolve eq5493 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5493
  have eq5758 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X4)) X3) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5465 X0 X1 X2 X3 X4
       have i₂ := eq263 X1 X0 (M.op (M.op X0 (M.op X1 X4)) X3) X2
       grind)
    | (have i₁ := eq5465 X4 X1 X3 X3 X4
       have i₂ := eq263 X1 (M.op (M.op X4 (M.op X1 X4)) X3) X3 X4
       grind)
    | exact superpose eq263 eq5465
    | exact resolve eq5465 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465
  have eq5782 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X4 X3))) = (M.op X2 (M.op X3 (M.op (M.op X1 X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5433 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X1 X0) X4 X3
       grind)
    | (have i₁ := eq5433 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X3 (M.op X1 X0))
       grind)
    | exact superpose eq101 eq5433
    | exact resolve eq5433 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5433
  have eq5897 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X0 (M.op X1 X4)) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5758 X0 X1 X2 X3 X4
       have i₂ := eq284 X0 X1 X2 (M.op (M.op X0 (M.op X1 X4)) X3)
       grind)
    | (have i₁ := eq5758 X0 X1 X2 X3 X4
       have i₂ := eq284 X0 (M.op (M.op X0 (M.op X1 X4)) X3) X2 X1
       grind)
    | exact superpose eq284 eq5758
    | exact resolve eq5758 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq5758
  have eq5914 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X4 X3))) = (M.op X2 (M.op X3 (M.op X1 (M.op X0 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5782 X0 X1 X2 X3 X4
       have i₂ := eq101 X0 X4 X1
       grind)
    | (have i₁ := eq5782 X0 X1 X2 X3 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq101 eq5782
    | exact resolve eq5782 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782
  have eq5970 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op X1 (M.op X2 (M.op X0 (M.op (M.op X1 X4) X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5897 X0 X1 X2 X3 X4
       have i₂ := eq101 (M.op X1 X4) X3 X0
       grind)
    | (have i₁ := eq5897 X0 X1 X2 (M.op X0 X1) X4
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X1 X4))
       grind)
    | exact superpose eq101 eq5897
    | exact resolve eq5897 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5897
  have eq5981 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X1 (M.op X0 X4)))) = (M.op X0 (M.op X1 (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5914 X0 X1 X2 X3 X4
       have i₂ := eq101 X1 (M.op X2 (M.op X4 X3)) X0
       grind)
    | (have i₁ := eq5914 X0 X1 X0 X3 X4
       have i₂ := eq101 X0 (M.op X4 X3) (M.op X0 X1)
       grind)
    | exact superpose eq101 eq5914
    | exact resolve eq5914 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5914
  have eq6029 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X1 (M.op X2 (M.op (M.op X1 X4) X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq5970 x X1 X2 X3 X4
       have i₂ := eq153 X1 X2 x (M.op (M.op X1 X4) X3)
       grind)
    | exact superpose eq153 eq5970
    | exact resolve eq5970 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq6073 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X1 (M.op X2 (M.op X1 (M.op X4 X3)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq6029 X1 X2 X3 X4
       have i₂ := eq101 X4 X3 X1
       grind)
    | (have i₁ := eq6029 X1 X2 (M.op x X1) X4
       have i₂ := eq101 x X1 (M.op X1 X4)
       grind)
    | exact superpose eq101 eq6029
    | exact resolve eq6029 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6029
  have eq6104 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X4 X3)) = (M.op X2 (M.op X3 X4)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq6073 x X2 X4 X3
       have i₂ := eq135 x X2 (M.op X3 X4)
       grind)
    | (have i₁ := eq6073 X2 X2 X3 X4
       have i₂ := eq135 x X2 (M.op X2 (M.op X2 (M.op X4 X3)))
       grind)
    | exact superpose eq135 eq6073
    | exact resolve eq6073 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6073
  have eq6447 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X2 (M.op X1 X4)))) = (M.op (M.op X5 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X5 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X5 X4 X3 (M.op X0 (M.op X2 (M.op X1 X4)))
       have i₂ := eq111 X4 X0 X1 X2
       grind)
    | exact superpose eq111 eq24
    | exact resolve eq24 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq6476 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X2 (M.op X1 X4)))) = (M.op X5 (M.op (M.op X5 (M.op X0 (M.op X1 X2))) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6447 X0 X1 X2 X3 X4 X5
       have i₂ := eq263 X4 X5 (M.op X5 (M.op X0 (M.op X1 X2))) X3
       grind)
    | (have i₁ := eq6447 X0 X1 X2 X3 X1 X4
       have i₂ := eq263 X1 (M.op X4 (M.op X0 (M.op X1 X2))) X3 X4
       grind)
    | exact superpose eq263 eq6447
    | exact resolve eq6447 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq6447
  have eq6575 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X2 (M.op X1 X4)))) = (M.op X5 (M.op X5 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq6476 X0 X1 X2 X3 X4 X5
       have i₂ := eq101 (M.op X0 (M.op X1 X2)) (M.op X3 X4) X5
       grind)
    | (have i₁ := eq6476 X0 X1 X2 X0 X1 X5
       have i₂ := eq101 X0 X1 (M.op X5 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq101 eq6476
    | exact resolve eq6476 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6476
  have eq6645 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X2 (M.op X1 X4)))) = (M.op (M.op X3 X4) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6575 X0 X1 X2 X3 X4 x
       have i₂ := eq320 x (M.op X3 X4) (M.op X0 (M.op X1 X2))
       grind)
    | (have i₁ := eq6575 X0 X1 X2 X3 X4 X2
       have i₂ := eq320 X0 X2 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X4)))
       grind)
    | exact superpose eq320 eq6575
    | exact resolve eq6575 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6575
  have eq6701 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op X3 (M.op X0 (M.op X2 (M.op X1 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6645 X0 X1 X2 X3 X4
       have i₂ := eq101 X4 (M.op X0 (M.op X1 X2)) X3
       grind)
    | (have i₁ := eq6645 X0 X1 X2 X3 X4
       have i₂ := eq101 X0 (M.op X1 X2) (M.op X3 X4)
       grind)
    | exact superpose eq101 eq6645
    | exact resolve eq6645 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6645
  have eq33700 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X2) = (M.op X3 (M.op X3 X1)) ∨ (k (M.op X0 (M.op X0 X0)) X2) = (M.op (M.op X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X0 X0 X0
       have i₂ := eq1242 X3 (M.op X0 (M.op X0 X0)) X1 X2
       grind)
    | exact superpose eq1242 eq24
    | (have j1 := eq1242 X3 (M.op X0 (M.op X0 X0)) X1 X2
       grind)
    | exact resolve eq24 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1242
  have eq33737 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X0 X0)) X2) = (M.op X0 (M.op (M.op X0 X0) X2)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X2) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33700 X0 X1 X2 X3
       have i₂ := eq101 (M.op X0 X0) X2 X0
       grind)
    | (have i₁ := eq33700 X0 X1 (M.op X0 X1) X3
       have i₂ := eq101 X0 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq101 eq33700
    | (have j0 := eq33700 X0 X0 X0 X0
       grind)
    | exact resolve eq33700 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33700
  have eq34069 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X0 X0)) X2) = (M.op X0 (M.op X0 (M.op X0 X2))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X2) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33737 X0 X1 X2 X3
       have i₂ := eq101 X0 X2 X0
       grind)
    | (have i₁ := eq33737 X0 X1 (M.op X0 X1) X3
       have i₂ := eq101 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq101 eq33737
    | (have j0 := eq33737 X0 X0 X0 X0
       grind)
    | exact resolve eq33737 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33737
  have eq34246 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (k (M.op X0 (M.op X0 X0)) X2) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X1 X2) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34069 X0 X1 X2 X3
       have i₂ := eq135 X0 X0 X2
       grind)
    | (have i₁ := eq34069 X2 X1 X2 X3
       have i₂ := eq135 X0 X2 (M.op X2 (M.op X2 X2))
       grind)
    | exact superpose eq135 eq34069
    | (have j0 := eq34069 X0 X0 X0 X0
       grind)
    | exact resolve eq34069 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq34069
  have eq62446 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X1)) ≠ (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 (M.op X2 (M.op X0 X2)) X1
       have i₂ := eq102 X0 X2 X2 (M.op X0 X2)
       grind)
    | exact superpose eq102 eq193
    | (have r₁ := eq193 (M.op X1 X1) X1
       have r₂ := eq102 X1 X1 (M.op X1 X1) X1
       grind)
    | exact resolve eq193 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq193
  have eq62541 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X1)) ≠ (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 (M.op X1 X0)))) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62446 X0 X1 X2
       have i₂ := eq113 (M.op X0 (M.op X1 X0)) X0 X1 (M.op X1 X0)
       grind)
    | (have i₁ := eq62446 X0 X1 X2
       have i₂ := eq113 (M.op X0 (M.op X1 X0)) X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq113 eq62446
    | (have j0 := eq62446 X0 X1 X2
       grind)
    | exact resolve eq62446 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62446
  have eq62590 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X1)) ≠ (M.op X1 (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)))) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62541 X0 X1 X2
       have i₂ := eq5981 X1 X1 (M.op X0 (M.op X1 X0)) X0 X0
       grind)
    | (have i₁ := eq62541 x x X2
       have i₂ := eq5981 (M.op x (M.op x x)) x x x x
       grind)
    | exact superpose eq5981 eq62541
    | (have j0 := eq62541 X0 X1 X2
       grind)
    | exact resolve eq62541 eq5981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62541
  have eq62634 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X1)) ≠ (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X1)) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62590 X0 X1 X2
       have i₂ := eq976 X1 X1 (M.op X0 (M.op X1 X0)) X0
       grind)
    | exact superpose eq976 eq62590
    | (have j0 := eq62590 X0 X1 X2
       grind)
    | exact resolve eq62590 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62590
  have eq62675 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X1)) ≠ (M.op X1 (M.op (M.op X0 (M.op X1 X0)) X1)) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62634 X0 X1 X2
       have i₂ := eq545 X1 (M.op X0 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq62634 X0 x X2
       have i₂ := eq545 (M.op X0 (M.op x X0)) x x
       grind)
    | exact superpose eq545 eq62634
    | (have j0 := eq62634 X0 X1 X2
       grind)
    | exact resolve eq62634 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62634
  have eq62711 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X1)) ≠ (M.op X1 (M.op X1 (M.op X0 (M.op X1 X0)))) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62675 X0 X1 X2
       have i₂ := eq545 X1 X1 (M.op X0 (M.op X1 X0))
       grind)
    | (have i₁ := eq62675 X0 x X2
       have i₂ := eq545 x (M.op X0 (M.op x X0)) x
       grind)
    | exact superpose eq545 eq62675
    | (have j0 := eq62675 X0 X1 X2
       grind)
    | exact resolve eq62675 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62675
  have eq62745 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) ≠ (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62711 X0 X1 X2
       have i₂ := eq153 X1 X0 X1 X0
       grind)
    | exact superpose eq153 eq62711
    | (have j0 := eq62711 X0 X1 X2
       grind)
    | exact resolve eq62711 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62711
  have eq62776 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) ≠ (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62745 X0 X1 X2
       have i₂ := eq6104 X0 X1 (M.op X1 X0)
       grind)
    | (have i₁ := eq62745 X0 X1 X2
       have i₂ := eq6104 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq6104 eq62745
    | (have j0 := eq62745 X0 X1 X2
       grind)
    | exact resolve eq62745 eq6104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104 eq62745
  have eq62802 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) ∨ (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62776 X0 X1 X2
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq62776
    | (have j0 := eq62776 X0 X1 X2
       grind)
    | (have r₁ := eq62776 X2 (M.op X2 X2) X2
       have r₂ := eq9 (M.op X2 X2) (M.op X2 X2) X2
       grind)
    | exact resolve eq62776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62776
  have eq62828 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op X0 (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))))) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62802 X0 X1 X2
       have i₂ := eq6701 X0 (M.op X1 X0) X1 X2 (M.op X0 (M.op X1 X0))
       grind)
    | (have i₁ := eq62802 X2 x x
       have i₂ := eq6701 (M.op X2 (M.op x X2)) (M.op x X2) X2 x x
       grind)
    | exact superpose eq6701 eq62802
    | (have j0 := eq62802 X0 X1 X2
       grind)
    | (have r₁ := eq62802 (M.op X2 (M.op X1 x)) (M.op x (M.op (M.op X2 (M.op X1 x)) (M.op X1 X2))) X2
       have r₂ := eq6701 (M.op X2 (M.op X1 x)) X1 X2 (M.op x (M.op (M.op X2 (M.op X1 x)) (M.op X1 X2))) x
       grind)
    | (have r₁ := eq62802 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X2 (M.op X1 (M.op X0 (M.op X1 X2))))) X2
       have r₂ := eq6701 X0 X1 X2 (M.op X0 (M.op X2 (M.op X1 (M.op X0 (M.op X1 X2))))) (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq62802 eq6701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62802
  have eq62848 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X1)))) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62828 X0 X1 X2
       have i₂ := eq5734 X0 X1 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq5734 eq62828
    | (have j0 := eq62828 X0 X1 X2
       grind)
    | exact resolve eq62828 eq5734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5734 eq62828
  have eq62866 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) = (M.op X2 (M.op X1 (M.op X1 (M.op X0 (M.op X1 X0))))) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62848 X0 X1 X2
       have i₂ := eq6701 X1 X0 X1 X2 (M.op X1 X0)
       grind)
    | (have i₁ := eq62848 X1 x x
       have i₂ := eq6701 (M.op x X1) X1 x x x
       grind)
    | exact superpose eq6701 eq62848
    | (have j0 := eq62848 X0 X1 X2
       grind)
    | (have r₁ := eq62848 (M.op X2 (M.op X1 x)) (M.op x (M.op (M.op X2 (M.op X1 x)) (M.op X1 X2))) X2
       have r₂ := eq6701 (M.op X2 (M.op X1 x)) X1 X2 (M.op x (M.op (M.op X2 (M.op X1 x)) (M.op X1 X2))) x
       grind)
    | (have r₁ := eq62848 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X2 (M.op X1 (M.op X0 (M.op X1 X2))))) X2
       have r₂ := eq6701 X0 X1 X2 (M.op X0 (M.op X2 (M.op X1 (M.op X0 (M.op X1 X2))))) (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq62848 eq6701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6701 eq62848
  have eq62881 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) X1))) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62866 X0 X1 X2
       have i₂ := eq523 X1 (M.op X0 (M.op X1 X0)) X2
       grind)
    | exact superpose eq523 eq62866
    | (have j0 := eq62866 X0 X1 X2
       grind)
    | (have r₁ := eq62866 X0 (M.op X0 (M.op X0 (M.op X0 X0))) X2
       have r₂ := eq523 X0 (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact resolve eq62866 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq62866
  have eq62896 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 (M.op X1 X0)))) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62881 X0 X1 X2
       have i₂ := eq113 (M.op X0 (M.op X1 X0)) X0 X1 (M.op X1 X0)
       grind)
    | (have i₁ := eq62881 X0 X1 X2
       have i₂ := eq113 (M.op X0 (M.op X1 X0)) X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq113 eq62881
    | (have j0 := eq62881 X0 X1 X2
       grind)
    | (have r₁ := eq62881 (M.op X2 x) (M.op (M.op X2 x) (M.op x X2)) X2
       have r₂ := eq113 (M.op (M.op X2 x) (M.op x X2)) (M.op X2 x) X2 x
       grind)
    | (have r₁ := eq62881 (M.op x X2) (M.op (M.op x X2) (M.op X2 x)) X2
       have r₂ := eq113 (M.op (M.op x X2) (M.op X2 x)) (M.op x X2) X2 x
       grind)
    | exact resolve eq62881 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq62881
  have eq62910 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op X1 (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)))) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62896 X0 X1 X2
       have i₂ := eq5981 X1 X1 (M.op X0 (M.op X1 X0)) X0 X0
       grind)
    | (have i₁ := eq62896 x x X2
       have i₂ := eq5981 (M.op x (M.op x x)) x x x x
       grind)
    | exact superpose eq5981 eq62896
    | (have j0 := eq62896 X0 X1 X2
       grind)
    | exact resolve eq62896 eq5981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981 eq62896
  have eq62923 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X1)) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62910 X0 X1 X2
       have i₂ := eq976 X1 X1 (M.op X0 (M.op X1 X0)) X0
       grind)
    | exact superpose eq976 eq62910
    | (have j0 := eq62910 X0 X1 X2
       grind)
    | exact resolve eq62910 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq62910
  have eq62934 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op X1 (M.op (M.op X0 (M.op X1 X0)) X1)) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62923 X0 X1 X2
       have i₂ := eq545 X1 (M.op X0 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq62923 X0 x X2
       have i₂ := eq545 (M.op X0 (M.op x X0)) x x
       grind)
    | exact superpose eq545 eq62923
    | (have j0 := eq62923 X0 X1 X2
       grind)
    | exact resolve eq62923 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62923
  have eq62944 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op X1 (M.op X1 (M.op X0 (M.op X1 X0)))) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62934 X0 X1 X2
       have i₂ := eq545 X1 X1 (M.op X0 (M.op X1 X0))
       grind)
    | (have i₁ := eq62934 X0 x X2
       have i₂ := eq545 x (M.op X0 (M.op x X0)) x
       grind)
    | exact superpose eq545 eq62934
    | (have j0 := eq62934 X0 X1 X2
       grind)
    | exact resolve eq62934 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq62934
  have eq62953 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (k (M.op X1 (M.op X0 X0)) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62944 X0 X1 X2
       have i₂ := eq153 X1 X0 X1 X0
       grind)
    | exact superpose eq153 eq62944
    | (have j0 := eq62944 X0 X1 X2
       grind)
    | exact resolve eq62944 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq62944
  have eq62962 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 (M.op X0 X0)) X2) ∨ (M.op X1 X1) ≠ (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62953 X0 X1 X2
       have i₂ := eq5562 X2 X0 X1
       grind)
    | exact superpose eq5562 eq62953
    | (have j0 := eq62953 X0 X1 X2
       grind)
    | exact resolve eq62953 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562 eq62953
  have eq315008 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq478 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq315065 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq315008 X0 X1
       have j1 := eq34246 X0 X1 X1 x
       grind)
    | (have r₁ := eq315008 X0 X0
       have r₂ := eq34246 X0 X1 x x
       grind)
    | (have r₁ := eq315008 x x
       have r₂ := eq34246 X0 x x x
       grind)
    | (have r₁ := eq315008 X1 (M.op X1 X1)
       have r₂ := eq34246 X0 X1 (M.op X1 X1) X1
       grind)
    | exact resolve eq315008 eq34246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34246 eq315008
  have eq315068 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq315065 X0 X1
       have j1 := eq62962 X0 X0 X1
       grind)
    | (have r₁ := eq315065 X0 X1
       have r₂ := eq62962 X0 X0 x
       grind)
    | exact resolve eq315065 eq62962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62962 eq315065
  have eq315153 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315068 (M.op X1 X0) X2
       have i₂ := eq320 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq320 eq315068
    | exact resolve eq315068 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315068
  have eq315331 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315153 X0 X1 X2
       have i₂ := eq101 X0 X2 X1
       grind)
    | (have i₁ := eq315153 X0 X1 (M.op X0 X1)
       have i₂ := eq101 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq101 eq315153
    | exact resolve eq315153 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315153
  have eq380516 : ∀ X0 X1 X2 : G, (σ (k (k (τ (σ (M.op X1 X1))) X0) X2)) = (k (M.op (σ X0) (σ (M.op X1 X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X1 X1)) X0 X2
       have i₂ := eq371 X1 (σ X0)
       grind)
    | exact superpose eq371 eq22
    | exact resolve eq22 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq371
  have eq380523 : ∀ X0 X1 X2 : G, (σ (k (k (τ (σ (M.op X1 X1))) X0) X2)) = (M.op (σ (M.op X1 X1)) (M.op (σ X0) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq380516 X0 X1 X2
       have i₂ := eq315331 (σ X0) (σ (M.op X1 X1)) (σ X2)
       grind)
    | exact superpose eq315331 eq380516
    | exact resolve eq380516 eq315331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380516
  have eq380609 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k (k (τ (σ (M.op X1 X1))) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq380523 X0 X1 X2
       have i₂ := eq1601 X1 (σ X2) (σ X0)
       grind)
    | exact superpose eq1601 eq380523
    | exact resolve eq380523 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq380523
  have eq380668 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k (k (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq380609 X0 X1 X2
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq380609
    | exact resolve eq380609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380609
  have eq380705 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k (M.op X0 (M.op X1 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq380668 X0 X1 X2
       have i₂ := eq104 X1 X0
       grind)
    | exact superpose eq104 eq380668
    | exact resolve eq380668 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq380668
  have eq380732 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (M.op (M.op X1 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq380705 X0 X1 X2
       have i₂ := eq315331 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq315331 eq380705
    | exact resolve eq380705 eq315331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315331 eq380705
  have eq380747 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (M.op X1 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq380732 X0 X1 X2
       have i₂ := eq101 X1 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq380732 X0 X1 X1
       have i₂ := eq101 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq101 eq380732
    | exact resolve eq380732 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq380732
  have eq380753 : ∀ X0 X2 : G, (M.op (σ X2) (σ X0)) = (σ (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq380747 X0 x X2
       have i₂ := eq320 x X2 X0
       grind)
    | (have i₁ := eq380747 X0 X2 X2
       have i₂ := eq320 X0 X2 (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq320 eq380747
    | exact resolve eq380747 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq380747
  have eq382269 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq380753 y x
       grind)
    | exact superpose eq380753 eq16
    | (have r₁ := eq16
       have r₂ := eq380753 y x
       grind)
    | exact resolve eq16 eq380753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380753
  have eq382573 : False := by grind
  exact eq382573

/-- `Equation3456`: `x ◇ x = x ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3456 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3456 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq75 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq77 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq77
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq77 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq149 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq182 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq220 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq182 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq220 (σ X0)
       grind)
    | exact superpose eq220 eq15
    | exact resolve eq15 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq319
    | exact resolve eq319 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq319
  have eq532 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq538 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0)
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq77
    | exact resolve eq77 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq538
    | exact resolve eq538 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq552 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq532 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq532
    | exact resolve eq532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq554 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq550 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq550
    | exact resolve eq550 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq550
  have eq556 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq552
  have eq898 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq10
    | (have j1 := eq51 X1 X0
       grind)
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1000 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq898
    | (have j0 := eq898 X0 X1
       grind)
    | exact resolve eq898 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq1107 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1169 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X0 X1
       have i₂ := eq326 X1
       grind)
    | exact superpose eq326 eq1107
    | (have j0 := eq1107 X0 X1
       grind)
    | exact resolve eq1107 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq1107
  have eq4243 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1169 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1169 X0 X1
       grind)
    | exact superpose eq1169 eq10
    | (have j1 := eq1169 X0 X1
       grind)
    | exact resolve eq10 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq4450 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4243 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4243
    | (have j0 := eq4243 X0 X1
       grind)
    | exact resolve eq4243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq5503 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq5919 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5503
    | (have j0 := eq5503 X0 X1
       grind)
    | exact resolve eq5503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503
  have eq95610 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4450 y x
       grind)
    | exact superpose eq4450 eq16
    | (have j1 := eq4450 y x
       grind)
    | exact resolve eq16 eq4450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450
  have eq95781 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq5919 x y
       grind)
    | (have r₁ := eq95610
       have r₂ := eq5919 x y
       grind)
    | exact resolve eq95610 eq5919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5919 eq95610
  have eq97561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq556 y
       have i₂ := eq95781
       grind)
    | exact superpose eq95781 eq556
    | exact resolve eq556 eq95781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq95781
  have eq97640 : y = (M.op x x) := by
    first
    | (have r₁ := eq97561
       have r₂ := eq16
       grind)
    | exact resolve eq97561 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97561
  have eq100339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq554 x
       have i₂ := eq97640
       grind)
    | exact superpose eq97640 eq554
    | exact resolve eq554 eq97640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq97640
  have eq100418 : False := by grind
  exact eq100418

/-- `Equation3457`: `x ◇ x = x ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3457 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3457 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3457.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq140 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0
       have i₂ := eq48 X0 X1
       grind)
    | (have i₁ := eq80 X0
       have i₂ := eq48 X0 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq80
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq80 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq153 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq186 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq241 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq186 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq342 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq241 (σ X0)
       grind)
    | exact superpose eq241 eq15
    | exact resolve eq15 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq241 X0
       grind)
    | exact superpose eq241 eq342
    | exact resolve eq342 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq342
  have eq579 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq585 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (σ X0)
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq80
    | exact resolve eq80 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq585 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq585
    | exact resolve eq585 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq597 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq579 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq579
    | exact resolve eq579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq599 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq595
    | exact resolve eq595 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq595
  have eq601 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq597
  have eq1412 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1544 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1683 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1544 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1544
    | (have j0 := eq1544 X0 X1
       grind)
    | exact resolve eq1544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1760 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1683 X0 X1
       have i₂ := eq349 X1
       grind)
    | exact superpose eq349 eq1683
    | (have j0 := eq1683 X0 X1
       grind)
    | exact resolve eq1683 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq1683
  have eq5539 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1760 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1760 X0 X1
       grind)
    | exact superpose eq1760 eq10
    | (have j1 := eq1760 X0 X1
       grind)
    | exact resolve eq10 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq5786 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5539 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5539
    | (have j0 := eq5539 X0 X1
       grind)
    | exact resolve eq5539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq7013 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55
    | exact resolve eq55 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq7520 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7013 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7013
    | (have j0 := eq7013 X0 X1
       grind)
    | exact resolve eq7013 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq74081 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5786 y x
       grind)
    | exact superpose eq5786 eq16
    | (have j1 := eq5786 y x
       grind)
    | exact resolve eq16 eq5786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5786
  have eq74245 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7520 x y
       grind)
    | (have r₁ := eq74081
       have r₂ := eq7520 x y
       grind)
    | exact resolve eq74081 eq7520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7520 eq74081
  have eq75412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq601 y
       have i₂ := eq74245
       grind)
    | exact superpose eq74245 eq601
    | exact resolve eq601 eq74245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq74245
  have eq75501 : y = (M.op x x) := by
    first
    | (have r₁ := eq75412
       have r₂ := eq16
       grind)
    | exact resolve eq75412 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75412
  have eq75748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq599 x
       have i₂ := eq75501
       grind)
    | exact superpose eq75501 eq599
    | exact resolve eq599 eq75501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq75501
  have eq75838 : False := by grind
  exact eq75838

/-- `Equation3458`: `x ◇ x = x ◇ ((x ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3458 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3458 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3458.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq185 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0
       have i₂ := eq49 X0 X1
       grind)
    | (have i₁ := eq78 X0
       have i₂ := eq49 X0 (M.op X0 X0)
       grind)
    | exact superpose eq49 eq78
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq78 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq240 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq240 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq406 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq291 (σ X0)
       grind)
    | exact superpose eq291 eq15
    | exact resolve eq15 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq291 X0
       grind)
    | exact superpose eq291 eq406
    | exact resolve eq406 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq406
  have eq690 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq696 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq78 (σ X0)
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq78
    | exact resolve eq78 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq696 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq696
    | exact resolve eq696 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq703 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq690 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq690
    | exact resolve eq690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq709 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq701 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq701
    | exact resolve eq701 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq701
  have eq711 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq703
  have eq825 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq10
    | (have j1 := eq52 X1 X0
       grind)
    | exact resolve eq10 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq919 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq413 X0
       grind)
    | exact superpose eq413 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1019 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq919 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq919
    | (have j0 := eq919 X0 X1
       grind)
    | exact resolve eq919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1081 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq413 X1
       grind)
    | exact superpose eq413 eq1019
    | (have j0 := eq1019 X0 X1
       grind)
    | exact resolve eq1019 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq1019
  have eq5145 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1081 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1081 X0 X1
       grind)
    | exact superpose eq1081 eq10
    | (have j1 := eq1081 X0 X1
       grind)
    | exact resolve eq10 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq5381 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5145 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5145
    | (have j0 := eq5145 X0 X1
       grind)
    | exact resolve eq5145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5145
  have eq6562 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7032 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6562 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6562
    | (have j0 := eq6562 X0 X1
       grind)
    | exact resolve eq6562 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562
  have eq96901 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5381 y x
       grind)
    | exact superpose eq5381 eq16
    | (have j1 := eq5381 y x
       grind)
    | exact resolve eq16 eq5381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq97441 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7032 x y
       grind)
    | (have r₁ := eq96901
       have r₂ := eq7032 x y
       grind)
    | exact resolve eq96901 eq7032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7032 eq96901
  have eq100976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq711 y
       have i₂ := eq97441
       grind)
    | exact superpose eq97441 eq711
    | exact resolve eq711 eq97441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq97441
  have eq101070 : y = (M.op x x) := by
    first
    | (have r₁ := eq100976
       have r₂ := eq16
       grind)
    | exact resolve eq100976 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100976
  have eq103015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq709 x
       have i₂ := eq101070
       grind)
    | exact superpose eq101070 eq709
    | exact resolve eq709 eq101070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq101070
  have eq103109 : False := by grind
  exact eq103109

/-- `Equation3464`: `x ◇ x = x ◇ ((y ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3464 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3464 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3464.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq79 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq228 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0
       have i₂ := eq51 X0 X1
       grind)
    | (have i₁ := eq81 X0
       have i₂ := eq51 X0 (M.op X0 X0)
       grind)
    | exact superpose eq51 eq81
    | (have j1 := eq51 X1 X0
       grind)
    | exact resolve eq81 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq243 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq395 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq243 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq396 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq484 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq396 (σ X0)
       grind)
    | exact superpose eq396 eq15
    | exact resolve eq15 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq484 X0
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq484
    | exact resolve eq484 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq484
  have eq651 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq657 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq81
    | exact resolve eq81 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq657
    | exact resolve eq657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq666 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq651 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq651
    | exact resolve eq651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq669 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq663 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq663
    | exact resolve eq663 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq663
  have eq672 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq666
  have eq1274 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1394 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1274 X0 X1
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq1274
    | (have j0 := eq1274 X0 X1
       grind)
    | exact resolve eq1274 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1526 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1394 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1394
    | (have j0 := eq1394 X0 X1
       grind)
    | exact resolve eq1394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1592 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1526 X0 X1
       have i₂ := eq491 X1
       grind)
    | exact superpose eq491 eq1526
    | (have j0 := eq1526 X0 X1
       grind)
    | exact resolve eq1526 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq1526
  have eq5093 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1592 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1592 X0 X1
       grind)
    | exact superpose eq1592 eq10
    | (have j1 := eq1592 X0 X1
       grind)
    | exact resolve eq10 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq5339 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5093 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5093
    | (have j0 := eq5093 X0 X1
       grind)
    | exact resolve eq5093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq6661 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55
    | exact resolve eq55 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq7061 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6661 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6661
    | (have j0 := eq6661 X0 X1
       grind)
    | exact resolve eq6661 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6661
  have eq107864 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5339 y x
       grind)
    | exact superpose eq5339 eq16
    | (have j1 := eq5339 y x
       grind)
    | exact resolve eq16 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339
  have eq108047 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7061 x y
       grind)
    | (have r₁ := eq107864
       have r₂ := eq7061 x y
       grind)
    | exact resolve eq107864 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7061 eq107864
  have eq110032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq672 y
       have i₂ := eq108047
       grind)
    | exact superpose eq108047 eq672
    | exact resolve eq672 eq108047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq108047
  have eq110116 : y = (M.op x x) := by
    first
    | (have r₁ := eq110032
       have r₂ := eq16
       grind)
    | exact resolve eq110032 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110032
  have eq111925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq669 x
       have i₂ := eq110116
       grind)
    | exact superpose eq110116 eq669
    | exact resolve eq669 eq110116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq110116
  have eq112027 : False := by grind
  exact eq112027

/-- `Equation3472`: `x ◇ x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation3472 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3472 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3472.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq66 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq58 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq68 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq54 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X2 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq67 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq67 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq250 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X3 X2) = (k X2 X3) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq66 X2 X3 X0
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq66 X1 X0 X1
       grind)
    | (have r₁ := eq13 X0 X2
       have r₂ := eq66 X0 X1 X2
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq66 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X3 X2) = (k X2 X3) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq250 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq275 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq277 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X3 X2) = (k X2 X3) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq273 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq273 X0 X0 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq275 (σ X0)
       grind)
    | exact superpose eq275 eq15
    | exact resolve eq15 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq275 (τ X0)
       grind)
    | exact superpose eq275 eq32
    | exact resolve eq32 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq287
    | exact resolve eq287 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq293 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq284
    | exact resolve eq284 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq284
  have eq361 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq68 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq68 eq15
    | (have j1 := eq68 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq375 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq361 X0 X1 X2
       have i₂ := eq293 X1
       grind)
    | exact superpose eq293 eq361
    | (have j0 := eq361 X0 X1 X2
       grind)
    | exact resolve eq361 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq394 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq395 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq395 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq461 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (k X2 (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq70 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq70 eq15
    | (have j1 := eq70 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq473 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq470 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq470 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq480 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq461 X0 X1 X2
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq461
    | (have j0 := eq461 X0 X1 X2
       grind)
    | exact resolve eq461 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq499 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (M.op X0 X0))) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 (τ X0) X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq406
    | (have j0 := eq406 (τ X0) X1
       grind)
    | exact resolve eq406 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2017 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ X0)) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2005 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2005
    | (have j0 := eq2005 X0 X1
       grind)
    | exact resolve eq2005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2021 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2017 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2017
    | (have j0 := eq2017 X0 X1
       grind)
    | exact resolve eq2017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2022 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2021 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2021
    | (have j0 := eq2021 X0 X1
       grind)
    | exact resolve eq2021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2375 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq277 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq2382 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2418 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2382 X0 X1
       have i₂ := eq2382 X1 X0
       grind)
    | exact superpose eq2382 eq2382
    | (have j0 := eq2382 X0 X1
       have j1 := eq2382 X0 X1
       grind)
    | exact resolve eq2382 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2382 (σ X1) (σ X0)
       grind)
    | exact superpose eq2382 eq15
    | (have j1 := eq2382 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2490 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq2382 (τ X1) (τ X0)
       grind)
    | exact superpose eq2382 eq32
    | (have j1 := eq2382 (τ X1) (τ X0)
       grind)
    | exact resolve eq32 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2501 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2490 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq2490
    | (have j0 := eq2490 X0 X1
       grind)
    | exact resolve eq2490 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2490
  have eq2504 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2481 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2481
    | (have j0 := eq2481 X0 X1
       grind)
    | exact resolve eq2481 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq2522 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2418 X0 X1
       have j1 := eq473 X0 X1
       grind)
    | (have r₁ := eq2418 X0 X1
       have r₂ := eq473 X0 X1
       grind)
    | (have r₁ := eq2418 X1 X0
       have r₂ := eq473 X0 X1
       grind)
    | exact resolve eq2418 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2817 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4273 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | (have j0 := eq63 X0 X0
       grind)
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq4502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4273 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4273
    | (have j0 := eq4273 X0 X0
       grind)
    | exact resolve eq4273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq9910 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq4502 X0 X2
       grind)
    | exact superpose eq4502 eq394
    | (have j0 := eq394 X0 X1
       have j1 := eq4502 X0 X2
       grind)
    | exact resolve eq394 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9995 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq4502 X2 X0
       grind)
    | exact superpose eq4502 eq406
    | (have j0 := eq406 X0 X1
       have j1 := eq4502 X2 X0
       grind)
    | exact resolve eq406 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq4502
  have eq10067 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq9995 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9995
  have eq10079 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq9910 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9910
  have eq27459 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq375 X1 X0 X2
       grind)
    | exact superpose eq375 eq10
    | (have j1 := eq375 X1 X0 X2
       grind)
    | exact resolve eq10 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq27811 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27459 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27459
    | (have j0 := eq27459 X0 X1 X2
       grind)
    | exact resolve eq27459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27459
  have eq28708 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq480 X0 X1 X2
       grind)
    | exact superpose eq480 eq10
    | (have j1 := eq480 X0 X1 X2
       grind)
    | exact resolve eq10 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq29073 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28708 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28708
    | (have j0 := eq28708 X0 X1 X2
       grind)
    | exact resolve eq28708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28708
  have eq69783 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69784 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq71334 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq69783 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq69783
    | exact resolve eq69783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69783
  have eq71393 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71334 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq71334
    | (have j0 := eq71334 X0 X1
       grind)
    | exact resolve eq71334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71334
  have eq71444 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71393 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq71393
    | (have j0 := eq71393 X0 X1
       grind)
    | exact resolve eq71393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71393
  have eq71483 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71444 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq71444
    | (have j0 := eq71444 X0 X1
       grind)
    | (have r₁ := eq71444 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq71444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71444
  have eq71507 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71483 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq71483
    | (have j0 := eq71483 X0 X1
       grind)
    | exact resolve eq71483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71483
  have eq71518 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71507 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71507
    | (have j0 := eq71507 X0 X1
       grind)
    | exact resolve eq71507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71507
  have eq71528 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71518 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq71518
    | (have j0 := eq71518 X0 X1
       grind)
    | exact resolve eq71518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71518
  have eq72721 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71528 X0 X1
       have i₂ := eq2522 X0 X1
       grind)
    | exact superpose eq2522 eq71528
    | (have j0 := eq71528 X1 X0
       have j1 := eq2522 X1 X0
       grind)
    | exact resolve eq71528 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71528
  have eq72930 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72721 X0 X1
       have j1 := eq2817 X1 X0
       grind)
    | (have r₁ := eq72721 X0 X1
       have r₂ := eq2817 X0 X1
       grind)
    | (have r₁ := eq72721 X1 X0
       have r₂ := eq2817 X0 X1
       grind)
    | exact resolve eq72721 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817 eq72721
  have eq74222 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72930 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq72930
    | (have j0 := eq72930 (σ X0) (σ X1)
       grind)
    | exact resolve eq72930 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74324 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74222 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq74222
    | (have j0 := eq74222 X0 X1
       grind)
    | exact resolve eq74222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74222
  have eq78448 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq69784 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq69784
    | exact resolve eq69784 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69784
  have eq78674 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq78448 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq78448
    | (have j0 := eq78448 X0 X1
       grind)
    | exact resolve eq78448 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq78448
  have eq78723 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq78674 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq78674
    | (have j0 := eq78674 X0 X1
       grind)
    | exact resolve eq78674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78674
  have eq78752 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq78723 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq78723
    | (have j0 := eq78723 X0 X1
       grind)
    | (have r₁ := eq78723 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq78723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78723
  have eq78763 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78752 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78752
    | (have j0 := eq78752 X0 X1
       grind)
    | exact resolve eq78752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78752
  have eq78773 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78763 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq78763
    | (have j0 := eq78763 X0 X1
       grind)
    | exact resolve eq78763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78763
  have eq78783 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78773 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq78773
    | (have j0 := eq78773 X0 X1
       grind)
    | exact resolve eq78773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78773
  have eq80080 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78783 X0 X1
       have i₂ := eq2522 X0 X1
       grind)
    | exact superpose eq2522 eq78783
    | (have j0 := eq78783 X0 X1
       have j1 := eq2522 X0 X1
       grind)
    | exact resolve eq78783 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522 eq78783
  have eq80306 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq80080 X0 X1
       have j1 := eq473 X0 X1
       grind)
    | (have r₁ := eq80080 X1 X0
       have r₂ := eq473 X0 X1
       grind)
    | (have r₁ := eq80080 X0 X1
       have r₂ := eq473 X0 X1
       grind)
    | exact resolve eq80080 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq80080
  have eq88068 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2504 x y
       grind)
    | exact superpose eq2504 eq16
    | (have j1 := eq2504 x y
       grind)
    | exact resolve eq16 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq123846 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq27811 y x X0
       grind)
    | exact superpose eq27811 eq16
    | (have j1 := eq27811 y x X0
       grind)
    | exact resolve eq16 eq27811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27811
  have eq123860 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq123846 X0
       have j1 := eq10079 x X0 y
       grind)
    | (have r₁ := eq123846 X0
       have r₂ := eq10079 x x y
       grind)
    | exact resolve eq123846 eq10079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10079 eq123846
  have eq123930 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq80306 X0 (σ x)
       have i₂ := eq123860 X0
       grind)
    | exact superpose eq123860 eq80306
    | (have j0 := eq80306 X0 (σ x)
       grind)
    | (have r₁ := eq80306 X0 (σ x)
       have r₂ := eq123860 X0
       grind)
    | exact resolve eq80306 eq123860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123860
  have eq123965 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq123930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123930
  have eq124020 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq29073 x y X0
       grind)
    | exact superpose eq29073 eq16
    | (have j1 := eq29073 x y X0
       grind)
    | exact resolve eq16 eq29073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29073
  have eq124034 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq124020 X0
       have j1 := eq10067 y X0 x
       grind)
    | (have r₁ := eq124020 X0
       have r₂ := eq10067 y x x
       grind)
    | exact resolve eq124020 eq10067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10067 eq124020
  have eq124099 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq80306 (σ y) X0
       have i₂ := eq124034 X0
       grind)
    | exact superpose eq124034 eq80306
    | (have j0 := eq80306 (σ y) X0
       grind)
    | (have r₁ := eq80306 (σ y) X0
       have r₂ := eq124034 X0
       grind)
    | exact resolve eq80306 eq124034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80306 eq124034
  have eq124142 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq124099 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124099
  have eq124278 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq123965 (σ X0)
       grind)
    | exact superpose eq123965 eq15
    | exact resolve eq15 eq123965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123965
  have eq124381 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq124142 (σ X0)
       grind)
    | exact superpose eq124142 eq15
    | exact resolve eq15 eq124142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124142
  have eq126092 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124278 y
       grind)
    | exact superpose eq124278 eq16
    | exact resolve eq16 eq124278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124278
  have eq126586 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124381 x
       grind)
    | exact superpose eq124381 eq16
    | exact resolve eq16 eq124381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124381
  have eq625264 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq396 X0 X1
       grind)
    | exact superpose eq396 eq10
    | (have j1 := eq396 X0 X1
       grind)
    | exact resolve eq10 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq625298 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq625264 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq625264
    | (have j0 := eq625264 X0 X1
       grind)
    | exact resolve eq625264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625264
  have eq625371 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq625298 X0 (σ X1)
       grind)
    | exact superpose eq625298 eq15
    | (have j1 := eq625298 X0 X0
       grind)
    | exact resolve eq15 eq625298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625298
  have eq625398 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625371 X0 X1
       have i₂ := eq293 X1
       grind)
    | exact superpose eq293 eq625371
    | (have j0 := eq625371 X0 X1
       grind)
    | exact resolve eq625371 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625371
  have eq642299 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (M.op X1 X1) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq499 X0 X1
       grind)
    | exact superpose eq499 eq11
    | (have j1 := eq499 X0 X1
       grind)
    | exact resolve eq11 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq642329 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq642299 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq642299
    | (have j0 := eq642299 X0 X1
       grind)
    | exact resolve eq642299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642299
  have eq642366 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0
       have i₂ := eq642329 (σ X0) X1
       grind)
    | exact superpose eq642329 eq293
    | (have j1 := eq642329 X1 X1
       grind)
    | exact resolve eq293 eq642329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642329
  have eq642417 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq642366 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq642366
    | (have j0 := eq642366 X0 X1
       grind)
    | exact resolve eq642366 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642366
  have eq642436 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72930 X0 X1
       have i₂ := eq642417 X0 X1
       grind)
    | exact superpose eq642417 eq72930
    | (have j0 := eq72930 X0 X1
       have j1 := eq642417 X0 X1
       grind)
    | (have r₁ := eq72930 X0 X1
       have r₂ := eq642417 X0 X1
       grind)
    | exact resolve eq72930 eq642417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72930 eq642417
  have eq642494 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq642436 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642436
  have eq646463 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq642494 (τ X1) X0
       grind)
    | exact superpose eq642494 eq18
    | (have j1 := eq642494 (τ X1) X0
       grind)
    | exact resolve eq18 eq642494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq642494
  have eq646529 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X1 X1))) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq646463 X0 X1
       have i₂ := eq290 X1
       grind)
    | exact superpose eq290 eq646463
    | (have j0 := eq646463 X0 X1
       grind)
    | exact resolve eq646463 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq646463
  have eq646533 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq646529 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq646529
    | (have j0 := eq646529 X0 X1
       grind)
    | exact resolve eq646529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646529
  have eq646535 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq646533 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq646533
    | (have j0 := eq646533 X0 X1
       grind)
    | exact resolve eq646533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646533
  have eq646706 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0
       have i₂ := eq646535 X1 (σ X0)
       grind)
    | exact superpose eq646535 eq293
    | (have j1 := eq646535 X1 X1
       grind)
    | exact resolve eq293 eq646535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq646535
  have eq646738 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq646706 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq646706
    | (have j0 := eq646706 X0 X1
       grind)
    | exact resolve eq646706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646706
  have eq646743 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq646738 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq646738
    | (have j0 := eq646738 X0 X1
       grind)
    | exact resolve eq646738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646738
  have eq1197708 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq625398 x y
       grind)
    | exact superpose eq625398 eq16
    | (have j1 := eq625398 x y
       grind)
    | exact resolve eq16 eq625398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625398
  have eq1197712 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq646743 y x
       grind)
    | (have r₁ := eq1197708
       have r₂ := eq646743 y x
       grind)
    | exact resolve eq1197708 eq646743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646743 eq1197708
  have eq1197764 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1197712
       grind)
    | exact superpose eq1197712 eq10
    | exact resolve eq10 eq1197712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197712
  have eq1197851 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1197764
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1197764
    | exact resolve eq1197764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197764
  have eq1197867 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq1197851
       grind)
    | exact superpose eq1197851 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1197851
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq1197851
       grind)
    | exact resolve eq12 eq1197851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197851
  have eq1198240 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1197867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197867
  have eq1198981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126586
       have i₂ := eq1198240 x
       grind)
    | exact superpose eq1198240 eq126586
    | exact resolve eq126586 eq1198240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126586 eq1198240
  have eq1199111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq1198981
  have eq1199112 : x = (M.op x x) := by grind
  clear eq1199111
  have eq1199189 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq1199112
       grind)
    | exact superpose eq1199112 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq1199112
       grind)
    | exact resolve eq12 eq1199112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199206 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq394 x X0
       have i₂ := eq1199112
       grind)
    | exact superpose eq1199112 eq394
    | (have j0 := eq394 x X0
       grind)
    | exact resolve eq394 eq1199112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq1199265 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2022 x X0
       have i₂ := eq1199112
       grind)
    | exact superpose eq1199112 eq2022
    | (have j0 := eq2022 x X0
       grind)
    | (have r₁ := eq2022 x x
       have r₂ := eq1199112
       grind)
    | exact resolve eq2022 eq1199112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199112
  have eq1199545 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1199265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199265
  have eq1199551 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1199206 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199206
  have eq1199553 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1199189 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199189
  have eq1200913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq88068
       have i₂ := eq1199545 y
       grind)
    | exact superpose eq1199545 eq88068
    | exact resolve eq88068 eq1199545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88068
  have eq1200918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq126092
       have i₂ := eq1199545 y
       grind)
    | exact superpose eq1199545 eq126092
    | exact resolve eq126092 eq1199545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126092
  have eq1200945 : y = (M.op y y) := by grind
  clear eq1200918
  have eq1200946 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq1200913
  have eq1200953 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1200946
       have i₂ := eq1199553 y
       grind)
    | exact superpose eq1199553 eq1200946
    | exact resolve eq1200946 eq1199553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200946
  have eq1201259 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2022 y X0
       have i₂ := eq1200945
       grind)
    | exact superpose eq1200945 eq2022
    | (have j0 := eq2022 y X0
       grind)
    | (have r₁ := eq2022 y x
       have r₂ := eq1200945
       grind)
    | exact resolve eq2022 eq1200945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq1200945
  have eq1201539 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq1201259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201259
  have eq1208851 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq1199551 (σ X0)
       grind)
    | exact superpose eq1199551 eq15
    | exact resolve eq15 eq1199551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199551
  have eq1209239 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1208851 X0
       have i₂ := eq1199553 X0
       grind)
    | exact superpose eq1199553 eq1208851
    | exact resolve eq1208851 eq1199553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199553 eq1208851
  have eq1214397 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1200953
       grind)
    | exact superpose eq1200953 eq16
    | exact resolve eq16 eq1200953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214470 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq74324 x y
       have i₂ := eq1200953
       grind)
    | exact superpose eq1200953 eq74324
    | (have j0 := eq74324 x y
       grind)
    | exact resolve eq74324 eq1200953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74324 eq1200953
  have eq1214540 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1214470
       have i₂ := eq1201539 x
       grind)
    | exact superpose eq1201539 eq1214470
    | exact resolve eq1214470 eq1201539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201539 eq1214470
  have eq1214541 : (σ (k y x)) = (M.op (σ y) (σ x)) := by grind
  clear eq1214540
  have eq1214557 : (σ (k y x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1214541
       have i₂ := eq1209239 y
       grind)
    | exact superpose eq1209239 eq1214541
    | exact resolve eq1214541 eq1209239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209239 eq1214541
  have eq1214564 : (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1214557
       have i₂ := eq1199545 y
       grind)
    | exact superpose eq1199545 eq1214557
    | exact resolve eq1214557 eq1199545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199545 eq1214557
  have eq1214570 : False := by grind
  exact eq1214570

/-- `Equation3472`: `x ◇ x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3472 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3472 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3472.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq79 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq166 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0
       have i₂ := eq48 X0 X1
       grind)
    | (have i₁ := eq81 X0
       have i₂ := eq48 X0 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq81
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq81 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq217 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq217 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq390 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq280 (σ X0)
       grind)
    | exact superpose eq280 eq15
    | exact resolve eq15 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq390
    | exact resolve eq390 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq390
  have eq651 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq660 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 (σ X0)
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq81
    | exact resolve eq81 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq660 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq660
    | exact resolve eq660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq675 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq651 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq651
    | exact resolve eq651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq678 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq672 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq672
    | exact resolve eq672 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq672
  have eq681 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq675
  have eq920 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1023 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq920 X0 X1
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq920
    | (have j0 := eq920 X0 X1
       grind)
    | exact resolve eq920 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1131 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1023
    | (have j0 := eq1023 X0 X1
       grind)
    | exact resolve eq1023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1191 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1131 X0 X1
       have i₂ := eq397 X1
       grind)
    | exact superpose eq397 eq1131
    | (have j0 := eq1131 X0 X1
       grind)
    | exact resolve eq1131 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq1131
  have eq5812 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1191 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1191 X0 X1
       grind)
    | exact superpose eq1191 eq10
    | (have j1 := eq1191 X0 X1
       grind)
    | exact resolve eq10 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq6071 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5812 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5812
    | (have j0 := eq5812 X0 X1
       grind)
    | exact resolve eq5812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5812
  have eq7232 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55
    | exact resolve eq55 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq7714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7232 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7232
    | (have j0 := eq7232 X0 X1
       grind)
    | exact resolve eq7232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7232
  have eq94812 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6071 y x
       grind)
    | exact superpose eq6071 eq16
    | (have j1 := eq6071 y x
       grind)
    | exact resolve eq16 eq6071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6071
  have eq95020 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7714 x y
       grind)
    | (have r₁ := eq94812
       have r₂ := eq7714 x y
       grind)
    | exact resolve eq94812 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7714 eq94812
  have eq96094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq681 y
       have i₂ := eq95020
       grind)
    | exact superpose eq95020 eq681
    | exact resolve eq681 eq95020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq95020
  have eq96166 : y = (M.op x x) := by
    first
    | (have r₁ := eq96094
       have r₂ := eq16
       grind)
    | exact resolve eq96094 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96094
  have eq97138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq678 x
       have i₂ := eq96166
       grind)
    | exact superpose eq96166 eq678
    | exact resolve eq678 eq96166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq96166
  have eq97246 : False := by grind
  exact eq97246
