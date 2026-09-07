import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4490`: `x ◇ (y ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxx_pyx_Equation4490 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4490 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4490.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq17
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) X3
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X2) X3 X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X3) X1
       have i₂ := eq9 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq23 x X1 X2 X3
       have i₂ := eq27 x X1 X1
       grind)
    | exact superpose eq27 eq23
    | exact resolve eq23 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
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
  have eq72 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
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
  have eq82 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq84 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq90 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq82 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq126 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X3) = (M.op (M.op X2 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X1 X3 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 x
       have i₂ := eq27 x X0 X1
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq237 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq236 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq237 (σ X0)
       grind)
    | exact superpose eq237 eq15
    | exact resolve eq15 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq237 (τ X0)
       grind)
    | exact superpose eq237 eq40
    | exact resolve eq40 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq250 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq237 X0
       grind)
    | exact superpose eq237 eq243
    | exact resolve eq243 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq252 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq241 X0
       have i₂ := eq237 X0
       grind)
    | exact superpose eq237 eq241
    | exact resolve eq241 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq241
  have eq330 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X0) X1) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq24 (M.op x x) X0 X1 X4
       have i₂ := eq26 x x X0 X1
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq365 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (σ X0) X2
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq9
    | exact resolve eq9 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (M.op X2 (σ (M.op X0 X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (σ X0) X1
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq27
    | exact resolve eq27 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq376 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 (σ X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) (σ X0) X1 X2
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq24
    | exact resolve eq24 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq9
    | exact resolve eq9 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) x
       have i₂ := eq29 X1 X0 x
       grind)
    | exact superpose eq29 eq9
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 X1
       have i₂ := eq29 X1 X1 X1
       grind)
    | exact superpose eq29 eq429
    | exact resolve eq429 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq512 : ∀ X0 X1 : G, (M.op (τ X0) (M.op X1 X1)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq9
    | exact resolve eq9 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op X1 (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X0 (σ X0) (σ X0) x
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq126
    | exact resolve eq126 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq874 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0 X0
       have i₂ := eq201 X0 X1
       grind)
    | exact superpose eq201 eq29
    | exact resolve eq29 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X0 (M.op X1 X1) X2
       have i₂ := eq201 X0 X1
       grind)
    | exact superpose eq201 eq24
    | exact resolve eq24 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq1059 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X2 X2)) ≠ (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2) ∨ (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) = (k (M.op (M.op X2 X2) (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X2 X2) (M.op X2 X2)) X3
       have i₂ := eq28 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 (M.op (M.op X2 X2) (M.op X2 X2)) X3
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op (M.op X4 X4) (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X2 X3 (M.op (M.op X4 X4) (M.op X4 X4)) X5
       have i₂ := eq28 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq28 eq24
    | exact resolve eq24 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1095 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1086 X0 X1 X2 X3 X4 x
       have i₂ := eq877 X3 (M.op X4 X4) x
       grind)
    | exact superpose eq877 eq1086
    | exact resolve eq1086 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1114 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X2 X2))) ≠ (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2) ∨ (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) = (k (M.op (M.op X2 X2) (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1059 X0 X1 X1 X3
       have i₂ := eq29 X1 X1 X1
       grind)
    | exact superpose eq29 eq1059
    | (have j0 := eq1059 X0 X1 X2 X3
       grind)
    | exact resolve eq1059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1209 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 (M.op X4 X4)))) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1095 X0 X1 X2 X3 X4
       have i₂ := eq29 X4 X4 X4
       grind)
    | exact superpose eq29 eq1095
    | exact resolve eq1095 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1224 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X2 X2))) ≠ (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2) ∨ (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) = (k (M.op (M.op X2 X2) (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1114 X0 X1 X2 X3
       have i₂ := eq473 X1 X2
       grind)
    | exact superpose eq473 eq1114
    | (have j0 := eq1114 X0 X1 X2 X3
       grind)
    | exact resolve eq1114 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq1114
  have eq1290 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op X3 (M.op X4 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1209 X0 X1 X2 X3 X4
       have i₂ := eq874 X4 X4
       grind)
    | exact superpose eq874 eq1209
    | exact resolve eq1209 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1304 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X2 X2))) ≠ (M.op (M.op X0 (M.op X1 (M.op X2 X2))) X2) ∨ (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) = (k (M.op (M.op X2 X2) (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1224 X0 X1 X2 X3
       have i₂ := eq874 X1 X2
       grind)
    | exact superpose eq874 eq1224
    | (have j0 := eq1224 X0 X1 X2 X3
       grind)
    | exact resolve eq1224 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1361 : ∀ X2 X3 : G, (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) = (k (M.op (M.op X2 X2) (M.op X2 X2)) X3) := by
    intro X2 X3
    first
    | (have j0 := eq1304 x x X2 X3
       grind)
    | (have r₁ := eq1304 x x X2 X3
       have r₂ := eq1290 x x X2 X2 X2
       grind)
    | exact resolve eq1304 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq1304
  have eq1397 : ∀ X2 X3 : G, (M.op X3 (M.op X2 (M.op X2 (M.op X2 X2)))) = (k (M.op X2 (M.op X2 (M.op X2 X2))) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq1361 x X3
       have i₂ := eq29 x x x
       grind)
    | exact superpose eq29 eq1361
    | exact resolve eq1361 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1419 : ∀ X2 X3 : G, (M.op X3 (M.op X2 (M.op X2 X2))) = (k (M.op X2 (M.op X2 X2)) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq1397 x X3
       have i₂ := eq874 x x
       grind)
    | exact superpose eq874 eq1397
    | exact resolve eq1397 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1428 : ∀ X2 X3 : G, (M.op X3 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq1419 X2 X3
       have i₂ := eq874 X3 X2
       grind)
    | exact superpose eq874 eq1419
    | exact resolve eq1419 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1572 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 X1 (M.op X2 X2) X1
       have i₂ := eq330 X1 X2 X0
       grind)
    | exact superpose eq330 eq24
    | exact resolve eq24 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq1791 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1792 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1791 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq1832 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1792 (σ X1) (σ X0)
       grind)
    | exact superpose eq1792 eq15
    | (have j1 := eq1792 X0 (σ X0)
       grind)
    | exact resolve eq15 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1837 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1792 X1 (τ X0)
       grind)
    | exact superpose eq1792 eq18
    | (have j1 := eq1792 X0 (τ X0)
       grind)
    | exact resolve eq18 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1893 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1837 X0 X1
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq1837
    | (have j0 := eq1837 X0 X1
       grind)
    | exact resolve eq1837 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq1837
  have eq1896 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1832 X0 X1
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq1832
    | (have j0 := eq1832 X0 X1
       grind)
    | exact resolve eq1832 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq2153 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 X1))) X0) = (σ (M.op (τ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq1428 X1 (τ X0)
       grind)
    | exact superpose eq1428 eq18
    | exact resolve eq18 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2632 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X2 X1) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq877 X0 (σ X0) X2
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq877
    | exact resolve eq877 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3952 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 (M.op X3 X1)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 X1) X2 X4
       have i₂ := eq1572 X0 X1 X2 X3
       grind)
    | exact superpose eq1572 eq9
    | exact resolve eq9 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq4767 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1 (σ X0) (σ X0)
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq365
    | exact resolve eq365 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4807 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ (M.op X0 X0))) = (M.op X2 (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365 (M.op X0 X0) X2 X1
       have i₂ := eq877 X0 X0 X0
       grind)
    | exact superpose eq877 eq365
    | exact resolve eq365 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4938 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (M.op X1 X1)
       have i₂ := eq365 X1 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq365 eq252
    | exact resolve eq252 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4939 : ∀ X1 : G, (M.op (σ X1) (M.op (σ X1) (σ X1))) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq4938 x X1
       have i₂ := eq372 X1 (σ X1) x
       grind)
    | exact superpose eq372 eq4938
    | exact resolve eq4938 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq4938
  have eq5025 : ∀ X0 X2 : G, (M.op X2 (σ (M.op X0 X0))) = (M.op X2 (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq4807 X0 x X2
       have i₂ := eq2632 X0 X2 x
       grind)
    | exact superpose eq2632 eq4807
    | exact resolve eq4807 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632 eq4807
  have eq5053 : ∀ X1 : G, (M.op (σ X1) (M.op (σ X1) (σ X1))) = (σ (M.op X1 (M.op X1 (M.op X1 X1)))) := by
    intro X1
    first
    | (have i₁ := eq4939 X1
       have i₂ := eq29 X1 X1 X1
       grind)
    | exact superpose eq29 eq4939
    | exact resolve eq4939 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4939
  have eq5120 : ∀ X1 : G, (σ (M.op X1 (M.op X1 X1))) = (M.op (σ X1) (M.op (σ X1) (σ X1))) := by
    intro X1
    first
    | (have i₁ := eq5053 X1
       have i₂ := eq874 X1 X1
       grind)
    | exact superpose eq874 eq5053
    | exact resolve eq5053 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053
  have eq5175 : ∀ X1 : G, (σ (M.op X1 (M.op X1 X1))) = (M.op (σ (M.op X1 X1)) (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq5120 X1
       have i₂ := eq377 X1 (σ X1)
       grind)
    | exact superpose eq377 eq5120
    | exact resolve eq5120 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5208 : ∀ X1 : G, (σ (M.op X1 (M.op X1 X1))) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq5175 X1
       have i₂ := eq4767 X1 X1
       grind)
    | exact superpose eq4767 eq5175
    | exact resolve eq5175 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767 eq5175
  have eq5538 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ (M.op X0 X0))) X1) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 (M.op X0 X0) X1 X2
       have i₂ := eq877 X0 X0 X0
       grind)
    | exact superpose eq877 eq376
    | exact resolve eq376 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5712 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) = (k (M.op (M.op X0 (σ X1)) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1428 (σ (M.op X1 X1)) X2
       have i₂ := eq376 X1 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X0
       grind)
    | exact superpose eq376 eq1428
    | exact resolve eq1428 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq1428
  have eq5834 : ∀ X1 X2 : G, (M.op X2 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) = (k (M.op (σ X1) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq5712 x X1 X2
       have i₂ := eq877 (σ X1) (σ (M.op X1 X1)) x
       grind)
    | exact superpose eq877 eq5712
    | exact resolve eq5712 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5712
  have eq5917 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5538 X0 X1 x
       have i₂ := eq649 X0 x X1
       grind)
    | exact superpose eq649 eq5538
    | exact resolve eq5538 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq5538
  have eq5937 : ∀ X1 X2 : G, (M.op X2 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) = (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq5834 X1 X2
       have i₂ := eq377 X1 (σ (M.op X1 X1))
       grind)
    | exact superpose eq377 eq5834
    | exact resolve eq5834 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq5834
  have eq5987 : ∀ X1 X2 : G, (M.op X2 (σ (M.op (M.op X1 X1) (M.op X1 X1)))) = (k (σ (M.op (M.op X1 X1) (M.op X1 X1))) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq5937 X1 X2
       have i₂ := eq252 (M.op X1 X1)
       grind)
    | exact superpose eq252 eq5937
    | exact resolve eq5937 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5937
  have eq6010 : ∀ X1 X2 : G, (M.op X2 (σ (M.op X1 (M.op X1 (M.op X1 X1))))) = (k (σ (M.op X1 (M.op X1 (M.op X1 X1)))) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq5987 X1 X2
       have i₂ := eq29 X1 X1 X1
       grind)
    | exact superpose eq29 eq5987
    | exact resolve eq5987 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5987
  have eq6022 : ∀ X1 X2 : G, (M.op X2 (σ (M.op X1 (M.op X1 X1)))) = (k (σ (M.op X1 (M.op X1 X1))) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq6010 X1 X2
       have i₂ := eq874 X1 X1
       grind)
    | exact superpose eq874 eq6010
    | exact resolve eq6010 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq6010
  have eq6030 : ∀ X1 X2 : G, (σ (M.op (τ X2) (M.op X1 X1))) = (M.op X2 (σ (M.op X1 (M.op X1 X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq6022 X1 X2
       have i₂ := eq2153 X2 X1
       grind)
    | exact superpose eq2153 eq6022
    | exact resolve eq6022 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq6022
  have eq6036 : ∀ X1 X2 : G, (σ (M.op (τ X2) (M.op X1 X1))) = (M.op X2 (σ (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq6030 X1 X2
       have i₂ := eq5025 X1 X2
       grind)
    | exact superpose eq5025 eq6030
    | exact resolve eq6030 eq5025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025 eq6030
  have eq14700 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 (M.op X0 X0))) X1) = (M.op (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3952 (σ X0) (σ (M.op X0 X0)) X1 X3 X2
       have i₂ := eq5208 X0
       grind)
    | exact superpose eq5208 eq3952
    | exact resolve eq3952 eq5208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5208
  have eq14704 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14700 X0 X1 X2 X3
       have i₂ := eq5917 X0 X1
       grind)
    | exact superpose eq5917 eq14700
    | exact resolve eq14700 eq5917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5917 eq14700
  have eq16009 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6036 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6036
    | exact resolve eq6036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16062 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6036 X1 X0
       have i₂ := eq512 X0 X1
       grind)
    | exact superpose eq512 eq6036
    | exact resolve eq6036 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq6036
  have eq21230 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X1)) (σ (M.op X2 X2))) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365 X2 (σ (M.op X1 X1)) (σ X0)
       have i₂ := eq16009 X0 X1
       grind)
    | exact superpose eq16009 eq365
    | exact resolve eq365 eq16009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq21248 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 (σ (M.op X1 X1)))) X2) = (M.op (σ (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3952 (σ X0) (σ (M.op X1 X1)) X2 X4 X3
       have i₂ := eq16009 X0 X1
       grind)
    | exact superpose eq16009 eq3952
    | exact resolve eq3952 eq16009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952
  have eq21252 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (σ (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21248 X0 X1 X2 x x
       have i₂ := eq14704 X1 X2 x x
       grind)
    | exact superpose eq14704 eq21248
    | exact resolve eq21248 eq14704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14704 eq21248
  have eq21269 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X1) (M.op X2 X2))) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21230 X0 X1 X2
       have i₂ := eq16009 (M.op X1 X1) X2
       grind)
    | exact superpose eq16009 eq21230
    | exact resolve eq21230 eq16009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21230
  have eq21343 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) (σ X2)) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq21269 x X1 X2
       have i₂ := eq21252 x X1 (σ X2)
       grind)
    | exact superpose eq21252 eq21269
    | exact resolve eq21269 eq21252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21252 eq21269
  have eq21396 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) (σ X2)) = (σ (M.op X1 (M.op X2 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq21343 X1 X2
       have i₂ := eq877 X1 X2 X1
       grind)
    | exact superpose eq877 eq21343
    | exact resolve eq21343 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq21343
  have eq22126 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16009 X0 X1
       have i₂ := eq16062 (σ X0) X1
       grind)
    | exact superpose eq16062 eq16009
    | exact resolve eq16009 eq16062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16009 eq16062
  have eq22176 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op (τ (σ (M.op X0 X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22126 X0 X1
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq22126
    | exact resolve eq22126 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22126
  have eq22368 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22176 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq22176
    | exact resolve eq22176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22176
  have eq23451 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X2))) = (σ (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22368 X1 X2
       have i₂ := eq24 X1 X1 X2 X0
       grind)
    | (have i₁ := eq22368 X1 X2
       have i₂ := eq24 X0 X1 X2 X1
       grind)
    | exact superpose eq24 eq22368
    | exact resolve eq22368 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22368
  have eq69158 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23451 X2 X0 X1
       have i₂ := eq21396 X0 X1
       grind)
    | exact superpose eq21396 eq23451
    | exact resolve eq23451 eq21396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21396 eq23451
  have eq437184 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq1893 X0 X1
       grind)
    | exact superpose eq1893 eq11
    | (have j1 := eq1893 X0 X1
       grind)
    | exact resolve eq11 eq1893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq437187 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq437184 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq437184
    | (have j0 := eq437184 X0 X1
       grind)
    | exact resolve eq437184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437184
  have eq437212 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0
       have i₂ := eq437187 (σ X0) X1
       grind)
    | exact superpose eq437187 eq252
    | (have j1 := eq437187 (σ X0) X1
       grind)
    | exact resolve eq252 eq437187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq437187
  have eq437222 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq437212 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq437212
    | (have j0 := eq437212 X0 X1
       grind)
    | exact resolve eq437212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437212
  have eq437227 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq437222 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq437222
    | (have j0 := eq437222 X0 X1
       grind)
    | exact resolve eq437222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437222
  have eq437281 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1896 x y
       grind)
    | exact superpose eq1896 eq16
    | (have j1 := eq1896 x x
       grind)
    | exact resolve eq16 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq437283 : (σ x) = (σ (M.op x x)) := by
    first
    | (have j1 := eq437227 x x
       grind)
    | (have r₁ := eq437281
       have r₂ := eq437227 x y
       grind)
    | exact resolve eq437281 eq437227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437227 eq437281
  have eq437321 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq437283
       grind)
    | exact superpose eq437283 eq10
    | exact resolve eq10 eq437283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437283
  have eq437471 : x = (M.op x x) := by
    first
    | (have i₁ := eq437321
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq437321
    | exact resolve eq437321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437321
  have eq437867 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq69158 x x x
       have i₂ := eq437471
       grind)
    | exact superpose eq437471 eq69158
    | exact resolve eq69158 eq437471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69158 eq437471
  have eq446779 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq437867 y
       grind)
    | exact superpose eq437867 eq16
    | (have r₁ := eq16
       have r₂ := eq437867 y
       grind)
    | exact resolve eq16 eq437867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437867
  have eq447115 : False := by grind
  exact eq447115

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation450 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law450 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq392 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq429 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq392 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq392
    | (have j0 := eq392 X0 X1
       grind)
    | exact resolve eq392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq112
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq112
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq112
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq798 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq797
  have eq8235 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq16
    | exact resolve eq16 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8241 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq798
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq798
       grind)
    | exact resolve eq13 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq8258 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8241
  have eq8259 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8258
  have eq8268 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8259
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8259
    | exact resolve eq8259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq19443 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq429 x y
       have i₂ := eq8268
       grind)
    | exact superpose eq8268 eq429
    | (have j0 := eq429 x y
       grind)
    | exact resolve eq429 eq8268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq19447 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq8268
       grind)
    | exact superpose eq8268 eq10
    | exact resolve eq10 eq8268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8268
  have eq19519 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19443
  have eq19556 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19447
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq19447
    | exact resolve eq19447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19447
  have eq19557 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19519
       have r₂ := eq8235
       grind)
    | exact resolve eq19519 eq8235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8235 eq19519
  have eq19560 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq19556
       have r₂ := eq13 x y
       grind)
    | exact resolve eq19556 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19556
  have eq20137 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq118 x y
       have i₂ := eq19560
       grind)
    | exact superpose eq19560 eq118
    | (have j0 := eq118 x y
       grind)
    | exact resolve eq118 eq19560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq19560
  have eq20153 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20137
  have eq20154 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20153
  have eq21429 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq20154
       grind)
    | exact superpose eq20154 eq16
    | exact resolve eq16 eq20154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20154
  have eq21643 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21429
       have i₂ := eq19557
       grind)
    | exact superpose eq19557 eq21429
    | exact resolve eq21429 eq19557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19557 eq21429
  have eq21644 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21643
  have eq21645 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq21644
  have eq21965 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21645
       grind)
    | exact superpose eq21645 eq10
    | exact resolve eq10 eq21645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21645
  have eq22067 : x = y ∨ x = y := by
    first
    | (have i₁ := eq21965
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21965
    | exact resolve eq21965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21965
  have eq22068 : x = y := by grind
  clear eq22067
  have eq22180 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22068
       grind)
    | exact superpose eq22068 eq16
    | exact resolve eq16 eq22068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22068
  have eq22181 : False := by grind
  exact eq22181

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation455 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq73 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26
    | exact resolve eq26 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
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
  have eq198 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq919 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq982 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq919 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq919
    | (have j0 := eq919 (M.op X1 X1) X1
       grind)
    | exact resolve eq919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq2037 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198 y x
       grind)
    | exact superpose eq198 eq16
    | (have j1 := eq198 y x
       grind)
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq16939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2037
       have i₂ := eq982 x y
       grind)
    | exact superpose eq982 eq2037
    | (have j1 := eq982 (M.op y y) y
       grind)
    | (have r₁ := eq2037
       have r₂ := eq982 x y
       grind)
    | (have r₁ := eq2037
       have r₂ := eq982 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2037
       have r₂ := eq982 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2037 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq2037
  have eq16940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16939
  have eq16941 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16940
  have eq16947 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq16941
       grind)
    | exact superpose eq16941 eq26
    | exact resolve eq26 eq16941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq16950 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq16941
       grind)
    | exact superpose eq16941 eq73
    | exact resolve eq73 eq16941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq16941
  have eq17820 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq16950 (σ x)
       grind)
    | exact superpose eq16950 eq16
    | exact resolve eq16 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950
  have eq19352 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17820
       have i₂ := eq16947 x
       grind)
    | exact superpose eq16947 eq17820
    | exact resolve eq17820 eq16947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16947 eq17820
  have eq19353 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19352
  have eq19354 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq19353
  have eq19597 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19354
       grind)
    | exact superpose eq19354 eq10
    | exact resolve eq10 eq19354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19354
  have eq19660 : x = y ∨ x = y := by
    first
    | (have i₁ := eq19597
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19597
    | exact resolve eq19597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq19661 : x = y := by grind
  clear eq19660
  have eq19907 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19661
       grind)
    | exact superpose eq19661 eq16
    | exact resolve eq16 eq19661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19661
  have eq19908 : False := by grind
  exact eq19908

/-- `Equation510`: `x = y ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation510 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law510 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law510.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq74 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq315 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq315 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq315
    | (have j0 := eq315 X0 X1
       grind)
    | exact resolve eq315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq74
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq74
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq74
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq74 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq723 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq722
  have eq6015 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq16
    | exact resolve eq16 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6016 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq723
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq723
       grind)
    | exact resolve eq13 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq6017 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6016
  have eq6018 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6017
  have eq6020 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6018
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6018
    | exact resolve eq6018 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq13189 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq349 x y
       have i₂ := eq6020
       grind)
    | exact superpose eq6020 eq349
    | (have j0 := eq349 x y
       grind)
    | exact resolve eq349 eq6020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq13191 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq6020
       grind)
    | exact superpose eq6020 eq10
    | exact resolve eq10 eq6020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020
  have eq13246 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13189
  have eq13281 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13191
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq13191
    | exact resolve eq13191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13191
  have eq13282 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13246
       have r₂ := eq6015
       grind)
    | exact resolve eq13246 eq6015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6015 eq13246
  have eq13285 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq13281
       have r₂ := eq13 x y
       grind)
    | exact resolve eq13281 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13281
  have eq13621 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq76 x y
       have i₂ := eq13285
       grind)
    | exact superpose eq13285 eq76
    | (have j0 := eq76 x y
       grind)
    | exact resolve eq76 eq13285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq13285
  have eq13624 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13621
  have eq13625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13624
  have eq13706 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq13625
       grind)
    | exact superpose eq13625 eq16
    | exact resolve eq16 eq13625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13625
  have eq13893 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13706
       have i₂ := eq13282
       grind)
    | exact superpose eq13282 eq13706
    | exact resolve eq13706 eq13282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13282 eq13706
  have eq13894 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13893
  have eq13895 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq13894
  have eq14073 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13895
       grind)
    | exact superpose eq13895 eq10
    | exact resolve eq10 eq13895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13895
  have eq14157 : x = y ∨ x = y := by
    first
    | (have i₁ := eq14073
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14073
    | exact resolve eq14073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14073
  have eq14158 : x = y := by grind
  clear eq14157
  have eq14553 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14158
       grind)
    | exact superpose eq14158 eq16
    | exact resolve eq16 eq14158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14158
  have eq14554 : False := by grind
  exact eq14554

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation58 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq27
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq19 X0 X1
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq10
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42 x y
       grind)
    | exact superpose eq42 eq16
    | (have j1 := eq42 x y
       grind)
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq19
    | (have j1 := eq42 X0 X1
       grind)
    | exact resolve eq19 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq151 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq272 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (M.op X0 (σ X1)) X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq38
    | (have j1 := eq32 X0 (σ X1)
       grind)
    | exact resolve eq38 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq38
  have eq1688 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq144
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq144
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq144
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq144
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq144 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq1689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1688
  have eq1898 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 (τ X1) (τ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq149
    | (have j0 := eq149 (τ X0) (τ X1)
       grind)
    | exact resolve eq149 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq149
  have eq1952 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1898 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1898
    | (have j0 := eq1898 X0 X1
       grind)
    | exact resolve eq1898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1956 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1952 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1952
    | (have j0 := eq1952 X0 X1
       grind)
    | exact resolve eq1952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq1958 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1956 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1956
    | (have j0 := eq1956 X0 X1
       grind)
    | exact resolve eq1956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq1959 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1958 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1958
    | (have j0 := eq1958 X0 X1
       grind)
    | exact resolve eq1958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq1960 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1959 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1959
    | (have j0 := eq1959 X0 X1
       grind)
    | exact resolve eq1959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq1961 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1960
    | (have j0 := eq1960 X0 X1
       grind)
    | exact resolve eq1960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq11334 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq272 (σ x) y
       have i₂ := eq1689
       grind)
    | exact superpose eq1689 eq272
    | exact resolve eq272 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq1689
  have eq11367 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq11334
  have eq11374 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11367
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11367
    | exact resolve eq11367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11367
  have eq11378 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq11374
       have r₂ := eq13 x y
       grind)
    | exact resolve eq11374 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374
  have eq11388 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq151 x y
       have i₂ := eq11378
       grind)
    | exact superpose eq11378 eq151
    | (have j0 := eq151 x y
       grind)
    | exact resolve eq151 eq11378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq11391 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1961 x y
       have i₂ := eq11378
       grind)
    | exact superpose eq11378 eq1961
    | (have j0 := eq1961 x y
       grind)
    | exact resolve eq1961 eq11378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961 eq11378
  have eq11396 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11391
  have eq11400 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11388
  have eq11401 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11400
  have eq12557 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq11401
       grind)
    | exact superpose eq11401 eq16
    | exact resolve eq16 eq11401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11401
  have eq12706 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12557
       have i₂ := eq11396
       grind)
    | exact superpose eq11396 eq12557
    | exact resolve eq12557 eq11396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396 eq12557
  have eq12707 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12706
  have eq12708 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq12707
  have eq12866 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12708
       grind)
    | exact superpose eq12708 eq10
    | exact resolve eq10 eq12708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12708
  have eq12941 : x = y ∨ x = y := by
    first
    | (have i₁ := eq12866
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12866
    | exact resolve eq12866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12866
  have eq12942 : x = y := by grind
  clear eq12941
  have eq13129 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12942
       grind)
    | exact superpose eq12942 eq16
    | exact resolve eq16 eq12942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12942
  have eq13130 : False := by grind
  exact eq13130

/-- `Equation618`: `x = x ◇ (x ◇ ((x ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = Y then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_x_pxy_x_Equation618 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law618 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law618.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) x) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 (M.op X0 x)
       have i₂ := eq23 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq42 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq27 X0
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq122 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq45 (τ X1) X0
       grind)
    | exact superpose eq45 eq19
    | (have j1 := eq45 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq45 (σ X1) (σ X0)
       grind)
    | exact superpose eq45 eq15
    | (have j1 := eq45 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq321 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122
    | exact resolve eq122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq347 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq321
    | (have j0 := eq321 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq321 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq955 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123 x y
       grind)
    | exact superpose eq123 eq16
    | (have j1 := eq123 x y
       grind)
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq955
       have i₂ := eq347 y x
       grind)
    | exact superpose eq347 eq955
    | (have j1 := eq347 (σ x) (σ y)
       grind)
    | (have r₁ := eq955
       have r₂ := eq347 y x
       grind)
    | (have r₁ := eq955
       have r₂ := eq347 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq955
       have r₂ := eq347 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq955 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq955
  have eq1013 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1012
  have eq1119 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1013
       grind)
    | exact superpose eq1013 eq10
    | exact resolve eq10 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1159 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1119
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1119
    | exact resolve eq1119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1160 : x = y := by grind
  clear eq1159
  have eq1264 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1160
       grind)
    | exact superpose eq1160 eq16
    | exact resolve eq16 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1265 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1264
       have i₂ := eq27 x
       grind)
    | exact superpose eq27 eq1264
    | exact resolve eq1264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1266 : False := by grind
  exact eq1266

/-- `Equation645`: `x = x ◇ (y ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation645 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law645 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law645.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq55 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq134 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1008 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55
    | exact resolve eq55 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1008
    | (have j0 := eq1008 X0 X1
       grind)
    | exact resolve eq1008 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq2110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq134
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq134
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq134
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq134
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq2111 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2110
  have eq19380 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2111
       grind)
    | exact superpose eq2111 eq16
    | exact resolve eq16 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19385 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2111
       grind)
    | exact superpose eq2111 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2111
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2111
       grind)
    | exact resolve eq13 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq19438 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19385
  have eq19439 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19438
  have eq19450 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19439
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19439
    | exact resolve eq19439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19439
  have eq34285 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1042 y x
       have i₂ := eq19450
       grind)
    | exact superpose eq19450 eq1042
    | (have j0 := eq1042 y x
       grind)
    | exact resolve eq1042 eq19450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq34286 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq19450
       grind)
    | exact superpose eq19450 eq10
    | exact resolve eq10 eq19450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19450
  have eq34369 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq34285
  have eq34405 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq34286
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34286
    | exact resolve eq34286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34286
  have eq34406 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq34369
       have r₂ := eq19380
       grind)
    | exact resolve eq34369 eq19380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19380 eq34369
  have eq34409 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq34405
       have r₂ := eq13 x y
       grind)
    | exact resolve eq34405 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34405
  have eq35033 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq140 x y
       have i₂ := eq34409
       grind)
    | exact superpose eq34409 eq140
    | (have j0 := eq140 x y
       grind)
    | exact resolve eq140 eq34409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq34409
  have eq35049 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35033
  have eq35050 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35049
  have eq35640 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq35050
       grind)
    | exact superpose eq35050 eq16
    | exact resolve eq16 eq35050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35050
  have eq36082 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35640
       have i₂ := eq34406
       grind)
    | exact superpose eq34406 eq35640
    | exact resolve eq35640 eq34406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34406 eq35640
  have eq36083 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36082
  have eq36084 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36083
  have eq36407 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36084
       grind)
    | exact superpose eq36084 eq10
    | exact resolve eq10 eq36084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36084
  have eq36528 : x = y ∨ x = y := by
    first
    | (have i₁ := eq36407
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36407
    | exact resolve eq36407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36407
  have eq36529 : x = y := by grind
  clear eq36528
  have eq36875 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36529
       grind)
    | exact superpose eq36529 eq16
    | exact resolve eq16 eq36529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36529
  have eq36876 : False := by grind
  exact eq36876

/-- `Equation653`: `x = x ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law653.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq48 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq155 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49 x y
       grind)
    | exact superpose eq49 eq16
    | (have j1 := eq49 x y
       grind)
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq979 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1016 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq979
    | (have j0 := eq979 X0 X1
       grind)
    | exact resolve eq979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1902 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq155
       have i₂ := eq1016 y x
       grind)
    | exact superpose eq1016 eq155
    | (have j1 := eq1016 (σ y) (σ x)
       grind)
    | (have r₁ := eq155
       have r₂ := eq1016 y x
       grind)
    | (have r₁ := eq155
       have r₂ := eq1016 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq155
       have r₂ := eq1016 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq155 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq1903 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1902
  have eq27000 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1903
       grind)
    | exact superpose eq1903 eq16
    | exact resolve eq16 eq1903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27006 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1903
       grind)
    | exact superpose eq1903 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1903
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1903
       grind)
    | exact resolve eq13 eq1903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq27116 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq27006
  have eq27117 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq27116
  have eq27119 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq27117
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq27117
    | exact resolve eq27117 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27117
  have eq28391 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1016 y x
       have i₂ := eq27119
       grind)
    | exact superpose eq27119 eq1016
    | (have j0 := eq1016 y x
       grind)
    | exact resolve eq1016 eq27119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq28392 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq27119
       grind)
    | exact superpose eq27119 eq10
    | exact resolve eq10 eq27119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27119
  have eq28455 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq28391
  have eq28487 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28392
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28392
    | exact resolve eq28392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28392
  have eq28488 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28455
       have r₂ := eq27000
       grind)
    | exact resolve eq28455 eq27000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27000 eq28455
  have eq28491 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq28487
       have r₂ := eq13 x y
       grind)
    | exact resolve eq28487 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28487
  have eq29238 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq162 x y
       have i₂ := eq28491
       grind)
    | exact superpose eq28491 eq162
    | (have j0 := eq162 x y
       grind)
    | exact resolve eq162 eq28491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq28491
  have eq29266 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29238
  have eq29267 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29266
  have eq29613 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq29267
       grind)
    | exact superpose eq29267 eq16
    | exact resolve eq16 eq29267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29267
  have eq30142 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29613
       have i₂ := eq28488
       grind)
    | exact superpose eq28488 eq29613
    | exact resolve eq29613 eq28488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28488 eq29613
  have eq30143 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30142
  have eq30144 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30143
  have eq30273 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30144
       grind)
    | exact superpose eq30144 eq10
    | exact resolve eq10 eq30144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30144
  have eq30359 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30273
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30273
    | exact resolve eq30273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30273
  have eq30360 : x = y := by grind
  clear eq30359
  have eq30858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30360
       grind)
    | exact superpose eq30360 eq16
    | exact resolve eq16 eq30360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30360
  have eq30859 : False := by grind
  exact eq30859
