import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_x_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq9
    | exact resolve eq9 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq77 X0 X2
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq75 (M.op X0 X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq85
    | exact resolve eq85 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1 (M.op X0 X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq85
    | exact resolve eq85 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq83 X1 X1 X0
       grind)
    | exact superpose eq83 eq85
    | exact resolve eq85 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X1 X2 X3
       have i₂ := eq99 X1 X2 X0
       grind)
    | (have i₁ := eq99 X1 X1 X2
       have i₂ := eq99 X1 X1 X1
       grind)
    | exact superpose eq99 eq99
    | exact resolve eq99 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X3 (M.op X1 (M.op X2 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X2 (M.op X0 X1)) X1 X2
       have i₂ := eq383 X0 X1 X2
       grind)
    | exact superpose eq383 eq99
    | exact resolve eq99 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0)) X2
       have i₂ := eq83 X0 X1 X2
       grind)
    | exact superpose eq83 eq99
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X2 X3 X1
       have i₂ := eq99 X1 X2 X0
       grind)
    | (have i₁ := eq83 X1 X1 X1
       have i₂ := eq99 X1 X1 X1
       grind)
    | exact superpose eq99 eq83
    | exact resolve eq83 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 (M.op X1 X2)
       have i₂ := eq99 X1 X2 X0
       grind)
    | (have i₁ := eq75 (M.op X1 X1)
       have i₂ := eq99 X1 X1 X1
       grind)
    | exact superpose eq99 eq75
    | exact resolve eq75 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X2 X0))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq432 X0 X1 X2 X3
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq432
    | exact resolve eq432 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq509 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq75 (M.op X0 X1)
       grind)
    | exact superpose eq75 eq433
    | exact resolve eq433 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99 (M.op X3 (M.op X1 (M.op X0 X2))) X0 X2
       have i₂ := eq433 X0 X1 X2 X3
       grind)
    | exact superpose eq433 eq99
    | exact resolve eq99 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq523 X0 X1 X2 X3 X4
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq523
    | exact resolve eq523 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq538 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq509
    | exact resolve eq509 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq509 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq509
    | exact resolve eq509 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 (M.op X2 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq83 X1 X2 X0
       grind)
    | exact superpose eq83 eq509
    | exact resolve eq509 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 X0 X1 X2
       have i₂ := eq539 (M.op X0 X2) X1
       grind)
    | exact superpose eq539 eq538
    | exact resolve eq538 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq639 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X0))) (M.op X1 (M.op X2 (M.op X3 X0)))) = (M.op (M.op X4 (M.op X5 X0)) (M.op X1 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq433 (M.op X1 (M.op X2 (M.op X3 X0))) X5 (M.op X0 X0) X4
       have i₂ := eq479 X0 X2 X3 X1
       grind)
    | exact superpose eq479 eq433
    | exact resolve eq433 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq642 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 X0)) (M.op X1 (M.op X2 (M.op X3 X0)))) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq639 X0 X1 X2 X3 X4 X5
       have i₂ := eq539 (M.op X2 (M.op X3 X0)) X1
       grind)
    | exact superpose eq539 eq639
    | exact resolve eq639 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq646 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 X0)) (M.op X1 (M.op X2 (M.op X3 X0)))) = (M.op X2 (M.op X1 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq642 X0 X1 X2 X3 X4 X5
       have i₂ := eq567 X2 X1 (M.op X3 X0)
       grind)
    | exact superpose eq567 eq642
    | exact resolve eq642 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq666 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X1 X0 X2
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq99
    | exact resolve eq99 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 X2 X1
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq83
    | exact resolve eq83 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (M.op X1 X0)
       have i₂ := eq539 X0 X1
       grind)
    | exact superpose eq539 eq75
    | exact resolve eq75 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq567 X1 X0 X0
       grind)
    | exact superpose eq567 eq689
    | exact resolve eq689 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq770 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X1 (M.op X0 X0) X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq666
    | exact resolve eq666 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq666 X0 (M.op X1 X0) X2
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq666
    | exact resolve eq666 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X3 (M.op X2 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq666 (M.op X1 X0) X0 X2
       have i₂ := eq666 X0 X1 X2
       grind)
    | (have i₁ := eq666 (M.op X1 X0) (M.op X2 X1) X2
       have i₂ := eq666 X0 X1 X2
       grind)
    | exact superpose eq666 eq666
    | exact resolve eq666 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq697 X2 X1
       have i₂ := eq666 X2 X1 X0
       grind)
    | (have i₁ := eq697 (M.op X2 X1) X1
       have i₂ := eq666 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq666 eq697
    | exact resolve eq697 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 (M.op X2 X1) (M.op X1 X0)
       have i₂ := eq666 X0 X1 X2
       grind)
    | (have i₁ := eq509 X0 (M.op X1 X0)
       have i₂ := eq666 X0 X1 X2
       grind)
    | exact superpose eq666 eq509
    | exact resolve eq509 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq841 X0 X1 X2
       have i₂ := eq539 X1 X2
       grind)
    | exact superpose eq539 eq841
    | exact resolve eq841 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq864 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq784 X0 X1 X2 X3
       have i₂ := eq667 X0 X1 X1
       grind)
    | exact superpose eq667 eq784
    | exact resolve eq784 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq871 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq777 X0 X1 X2
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq777
    | exact resolve eq777 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq941 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq433 (M.op X1 (M.op X2 X0)) X4 (M.op X0 X0) X3
       have i₂ := eq871 X0 X2 X1
       grind)
    | exact superpose eq871 eq433
    | exact resolve eq433 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 (M.op X1 (M.op X2 X0)) (M.op X0 X0)
       have i₂ := eq871 X0 X2 X1
       grind)
    | exact superpose eq871 eq509
    | exact resolve eq509 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq943 X0 X1 X2
       have i₂ := eq539 (M.op X2 X0) X1
       grind)
    | exact superpose eq539 eq943
    | exact resolve eq943 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq951 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq941 X0 X1 X2 X3 X4
       have i₂ := eq539 (M.op X2 X0) X1
       grind)
    | exact superpose eq539 eq941
    | exact resolve eq941 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq954 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq951 X0 X1 X2 X3 X4
       have i₂ := eq950 X0 X1 X2
       grind)
    | exact superpose eq950 eq951
    | exact resolve eq951 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq951
  have eq1120 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X2 X0)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq433 (M.op X2 X0) X0 (M.op X0 X1) X3
       have i₂ := eq795 X2 X0 X1
       grind)
    | exact superpose eq795 eq433
    | exact resolve eq433 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1121 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 (M.op X0 X1)
       have i₂ := eq795 X2 X0 X1
       grind)
    | exact superpose eq795 eq9
    | exact resolve eq9 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1121 X0 X1 X2
       have i₂ := eq539 X0 X2
       grind)
    | exact superpose eq539 eq1121
    | exact resolve eq1121 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1149 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1120 X0 X1 X2 X3
       have i₂ := eq539 X0 X2
       grind)
    | exact superpose eq539 eq1120
    | exact resolve eq1120 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1284 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op (M.op X1 X3) (M.op X2 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1148 (M.op X1 X3) (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq1148 X1 X3 X0
       grind)
    | exact superpose eq1148 eq1148
    | exact resolve eq1148 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X0 (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1148 (M.op X2 X0) (M.op X0 X0) X1
       have i₂ := eq77 X0 X2
       grind)
    | exact superpose eq77 eq1148
    | exact resolve eq1148 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1148 X0 (M.op X0 X0) X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1148
    | exact resolve eq1148 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1148 X2 X3 X1
       have i₂ := eq666 X2 X1 X0
       grind)
    | (have i₁ := eq1148 (M.op X2 X1) X1 X1
       have i₂ := eq666 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq666 eq1148
    | exact resolve eq1148 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1416 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X0 (M.op X2 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1286 X0 X1 X2
       have i₂ := eq567 X2 X1 X0
       grind)
    | exact superpose eq567 eq1286
    | exact resolve eq1286 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1418 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X1 (M.op X2 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1284 X0 X1 X2 X3
       have i₂ := eq567 X1 X2 X3
       grind)
    | exact superpose eq567 eq1284
    | exact resolve eq1284 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1468 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1293 X2 X1
       have i₂ := eq666 X2 X1 X0
       grind)
    | (have i₁ := eq1293 (M.op X2 X1) X1
       have i₂ := eq666 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq666 eq1293
    | exact resolve eq1293 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1496 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq795 X0 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq1293 X0 X1
       grind)
    | exact superpose eq1293 eq795
    | exact resolve eq795 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2071 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X2 X1 (M.op X0 X0) X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq441
    | exact resolve eq441 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X0 (M.op X0 X0) X1 X2
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq441
    | exact resolve eq441 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2323 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X3 X1) (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq457 X0 x (M.op (M.op X0 X1) (M.op X1 x))
       have i₂ := eq1468 X0 X1 x
       grind)
    | exact superpose eq1468 eq457
    | exact resolve eq457 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq2411 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X3 X1) (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2323 X0 X1 X3
       have i₂ := eq567 X0 (M.op X3 X1) X1
       grind)
    | exact superpose eq567 eq2323
    | exact resolve eq2323 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq3544 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X1 X2
       have i₂ := eq541 X0 X1 X2
       grind)
    | (have i₁ := eq539 X1 X2
       have i₂ := eq541 X2 X1 X2
       grind)
    | exact superpose eq541 eq539
    | exact resolve eq539 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq3545 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X2 X1 X3
       have i₂ := eq541 X0 X1 X2
       grind)
    | (have i₁ := eq99 X2 X1 X2
       have i₂ := eq541 X2 X1 X2
       grind)
    | exact superpose eq541 eq99
    | exact resolve eq99 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3546 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X1 X3 X2
       have i₂ := eq541 X0 X1 X2
       grind)
    | (have i₁ := eq83 X1 X1 X2
       have i₂ := eq541 X2 X1 X2
       grind)
    | exact superpose eq541 eq83
    | exact resolve eq83 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq541
  have eq4311 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X0 X1)) = (M.op (M.op X4 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3545 X0 (M.op X0 (M.op X1 X0)) (M.op X2 X0) X3
       have i₂ := eq667 X0 X1 X2
       grind)
    | exact superpose eq667 eq3545
    | exact resolve eq3545 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq4600 : ∀ X0 X1 X3 X4 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X4 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq4311 X0 X1 x X3 X4
       have i₂ := eq1149 X1 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq1149 eq4311
    | exact resolve eq4311 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq4311
  have eq5139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) (M.op X0 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1148 X1 X2 (M.op X0 X0)
       have i₂ := eq770 X0 X1
       grind)
    | (have i₁ := eq1148 X1 X1 (M.op X1 X1)
       have i₂ := eq770 X1 X1
       grind)
    | exact superpose eq770 eq1148
    | exact resolve eq1148 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5325 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op (M.op (M.op X1 X1) X0) (M.op X0 (M.op (M.op X1 X1) X0))) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq854 (M.op (M.op X1 X1) X0) X1 X2
       have i₂ := eq770 X1 X0
       grind)
    | (have i₁ := eq854 (M.op (M.op X0 X0) X1) X1 X2
       have i₂ := eq770 X0 X1
       grind)
    | exact superpose eq770 eq854
    | exact resolve eq854 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq5529 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op (M.op X1 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5325 X0 X1 X2
       have i₂ := eq667 X0 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact superpose eq667 eq5325
    | exact resolve eq5325 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq5325
  have eq5733 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) (M.op X0 X1)) = (M.op (M.op X3 (M.op X4 (M.op X2 X1))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq864 (M.op X0 X1) (M.op X2 X1) X4 X3
       have i₂ := eq3546 X2 X1 X0 X0
       grind)
    | exact superpose eq3546 eq864
    | exact resolve eq864 eq3546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq3546
  have eq5898 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X3 (M.op X4 (M.op X2 X1))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5733 X0 X1 X2 X3 X4
       have i₂ := eq3544 X2 X1 X0
       grind)
    | exact superpose eq3544 eq5733
    | exact resolve eq5733 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5733
  have eq7574 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X0 (M.op (M.op X3 X1) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1324 X3 X1 (M.op X2 X0) (M.op X0 X0)
       have i₂ := eq77 X0 X2
       grind)
    | exact superpose eq77 eq1324
    | exact resolve eq1324 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8169 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1416 (M.op X1 (M.op X2 X0)) X0 X2
       have i₂ := eq1416 X0 X1 X2
       grind)
    | exact superpose eq1416 eq1416
    | exact resolve eq1416 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8229 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X0 (M.op X2 (M.op X1 (M.op X2 X0))) X2
       have i₂ := eq1416 X0 X1 X2
       grind)
    | exact superpose eq1416 eq99
    | exact resolve eq99 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8279 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op (M.op X3 (M.op X1 (M.op X0 (M.op X1 X2)))) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2411 X0 (M.op X2 (M.op X1 (M.op X2 X0))) X3
       have i₂ := eq1416 X0 X1 X2
       grind)
    | exact superpose eq1416 eq2411
    | exact resolve eq2411 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8314 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8279 X0 X1 X2 x
       have i₂ := eq383 X1 (M.op X0 (M.op X1 X2)) x
       grind)
    | exact superpose eq383 eq8279
    | exact resolve eq8279 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8279
  have eq8336 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8229 X0 X1 X2 X3
       have i₂ := eq954 X2 X0 X1 X0 X1
       grind)
    | exact superpose eq954 eq8229
    | exact resolve eq8229 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8229
  have eq8339 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8169 X0 X1 X2
       have i₂ := eq646 X2 X1 X0 X1 X0 X1
       grind)
    | exact superpose eq646 eq8169
    | exact resolve eq8169 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq8169
  have eq8373 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8314 X0 X1 X2
       have i₂ := eq954 X2 X0 X1 X0 X1
       grind)
    | exact superpose eq954 eq8314
    | exact resolve eq8314 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314
  have eq8439 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8339 X0 X2 (M.op (M.op X0 X1) (M.op X1 X2))
       have i₂ := eq1468 X0 X1 X2
       grind)
    | exact superpose eq1468 eq8339
    | exact resolve eq8339 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq8339
  have eq10978 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
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
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11130 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq77 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11240 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq75 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq75
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq75 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq10978 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq11286 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11285
  have eq11322 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11130 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq11130
    | (have j0 := eq11130 X0 X1
       grind)
    | exact resolve eq11130 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11130
  have eq11713 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11286 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11286
  have eq11770 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11240 (M.op X1 X0) X0
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq11240
    | (have j0 := eq11240 (M.op X1 X0) X0
       grind)
    | exact resolve eq11240 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11887 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1293 X0 X1
       have i₂ := eq11240 X0 (M.op X1 X0)
       grind)
    | exact superpose eq11240 eq1293
    | (have j1 := eq11240 X0 (M.op X1 X0)
       grind)
    | exact resolve eq1293 eq11240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11999 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq11887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11887
  have eq12076 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11999 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq11999
    | (have j0 := eq11999 X0 X1
       grind)
    | exact resolve eq11999 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11999
  have eq12138 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11770 X0 X1
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq11770
    | (have j0 := eq11770 X0 X1
       grind)
    | exact resolve eq11770 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11770
  have eq12139 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12138
  have eq12227 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12076 (M.op X0 X0) X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12076
    | (have j0 := eq12076 X0 X0
       grind)
    | exact resolve eq12076 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12275 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12227 X0
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12227
    | (have j0 := eq12227 X0
       grind)
    | exact resolve eq12227 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq12766 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0
       have i₂ := eq11713 X0 X1
       grind)
    | exact superpose eq11713 eq75
    | (have j1 := eq11713 X0 X1
       grind)
    | exact resolve eq75 eq11713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11713
  have eq13083 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11322 (M.op X0 X1) X0
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq11322
    | (have j0 := eq11322 (M.op X0 X1) X0
       grind)
    | exact resolve eq11322 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13414 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13083 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq13083
    | (have j0 := eq13083 X0 X1
       grind)
    | exact resolve eq13083 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13083
  have eq13415 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13414
  have eq13533 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13415 X1 (M.op X0 X1)
       have i₂ := eq11322 X0 X1
       grind)
    | exact superpose eq11322 eq13415
    | (have j1 := eq11322 X0 X1
       grind)
    | exact resolve eq13415 eq11322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11322 eq13415
  have eq13559 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533
  have eq13578 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq13559 (σ X1) X0
       grind)
    | exact superpose eq13559 eq26
    | (have j1 := eq13559 (k (τ X0) X1) (τ (M.op X0 (σ X1)))
       grind)
    | exact resolve eq26 eq13559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq13579 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq13559 (τ X1) X0
       grind)
    | exact superpose eq13559 eq19
    | (have j1 := eq13559 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq13559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq13559 (σ X1) (σ X0)
       grind)
    | exact superpose eq13559 eq15
    | (have j1 := eq13559 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq13559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13592 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 X0
       have i₂ := eq13559 (τ X1) (τ X0)
       grind)
    | exact superpose eq13559 eq38
    | (have j1 := eq13559 (τ (k X0 X1)) (M.op (τ X0) (τ X1))
       grind)
    | exact resolve eq38 eq13559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13606 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13578 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13578
    | exact resolve eq13578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13627 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13606 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq13606
    | (have j0 := eq13606 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq13606 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq13606
  have eq13654 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 X1)) = (σ (k X2 (τ (M.op X0 X1)))) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (k X0 X1) X2
       have i₂ := eq13627 X1 X0
       grind)
    | exact superpose eq13627 eq19
    | (have j1 := eq13627 (k (σ X2) (k X0 X1)) (σ (k X2 (τ (M.op X0 X1))))
       grind)
    | exact resolve eq19 eq13627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13655 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (σ (k (τ (M.op X0 X1)) X2)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X1) X2
       have i₂ := eq13627 X1 X0
       grind)
    | exact superpose eq13627 eq18
    | (have j1 := eq13627 (k (k X0 X1) (σ X2)) (σ (k (τ (M.op X0 X1)) X2))
       grind)
    | exact resolve eq18 eq13627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13627
  have eq13662 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13655 X0 X1 X2
       have i₂ := eq18 (M.op X0 X1) X2
       grind)
    | exact superpose eq18 eq13655
    | (have j0 := eq13655 (k (k X0 X1) (σ X2)) (k (M.op X0 X1) (σ X2)) X2
       grind)
    | exact resolve eq13655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13655
  have eq13663 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 X1)) = (k (σ X2) (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13654 X0 X1 X2
       have i₂ := eq19 (M.op X0 X1) X2
       grind)
    | exact superpose eq19 eq13654
    | (have j0 := eq13654 (k (σ X2) (k X0 X1)) (k (σ X2) (M.op X0 X1)) X2
       grind)
    | exact resolve eq13654 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13654
  have eq13673 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13579 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13579
    | exact resolve eq13579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13579
  have eq13719 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13673 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq13673
    | (have j0 := eq13673 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq13673 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13673
  have eq13918 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13583 x y
       grind)
    | exact superpose eq13583 eq16
    | (have j1 := eq13583 x y
       grind)
    | exact resolve eq16 eq13583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13918
       have i₂ := eq13719 y x
       grind)
    | exact superpose eq13719 eq13918
    | (have j1 := eq13719 (σ x) (σ y)
       grind)
    | (have r₁ := eq13918
       have r₂ := eq13719 y x
       grind)
    | (have r₁ := eq13918
       have r₂ := eq13719 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq13918
       have r₂ := eq13719 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq13918 eq13719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13719 eq13918
  have eq14036 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq14035
  have eq14041 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14036
       grind)
    | exact superpose eq14036 eq10
    | exact resolve eq10 eq14036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14036
  have eq14078 : x = y ∨ x = y := by
    first
    | (have i₁ := eq14041
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14041
    | exact resolve eq14041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14041
  have eq14079 : x = y := by grind
  clear eq14078
  have eq14080 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14079
       grind)
    | exact superpose eq14079 eq16
    | exact resolve eq16 eq14079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14079
  have eq14734 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13663 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13663
    | (have j0 := eq13663 (k X0 (k X1 X2)) (k X0 (M.op X1 X2)) X2
       grind)
    | exact resolve eq13663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13663
  have eq14840 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq14734
  have eq17317 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12766 X0 X1
       have i₂ := eq13559 X1 X0
       grind)
    | exact superpose eq13559 eq12766
    | (have j0 := eq12766 X0 X1
       have j1 := eq13559 (M.op X0 (M.op X0 X1)) X0
       grind)
    | (have r₁ := eq12766 X0 X1
       have r₂ := eq13559 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq12766 X0 X1
       have r₂ := eq13559 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12766 eq13559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13559
  have eq17319 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12766 X0 (M.op X1 X0)
       have i₂ := eq12139 X0 X1
       grind)
    | exact superpose eq12139 eq12766
    | (have j0 := eq12766 X0 (M.op X1 X0)
       have j1 := eq12139 X0 X1
       grind)
    | (have r₁ := eq12766 X1 (M.op X1 X1)
       have r₂ := eq12139 (M.op X1 X1) X1
       grind)
    | exact resolve eq12766 eq12139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12139 eq12766
  have eq17437 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17319
  have eq17439 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17317
  have eq17474 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17437 X0 X1
       have i₂ := eq1293 X0 X1
       grind)
    | exact superpose eq1293 eq17437
    | (have j0 := eq17437 X0 X1
       grind)
    | exact resolve eq17437 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17437
  have eq17475 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17474 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17474
  have eq23608 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X2 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq1416 X0 X1 X2
       grind)
    | exact superpose eq1416 eq567
    | exact resolve eq567 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq23872 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23608 X0 X1 X2
       have i₂ := eq436 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq436 eq23608
    | exact resolve eq23608 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23608
  have eq23915 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23872 X0 X1 X2
       have i₂ := eq954 X2 X0 X1 X0 X1
       grind)
    | exact superpose eq954 eq23872
    | exact resolve eq23872 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq23872
  have eq33213 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17439 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq1293 X0 X1
       grind)
    | exact superpose eq1293 eq17439
    | (have j0 := eq17439 (M.op X1 (M.op X0 X1)) X1
       grind)
    | (have r₁ := eq17439 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq1293 X0 X0
       grind)
    | exact resolve eq17439 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33479 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1 X1 X0
       have i₂ := eq17439 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact superpose eq17439 eq441
    | (have j1 := eq17439 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq441 eq17439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq33498 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq33479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33479
  have eq33536 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33213
  have eq33548 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33498 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq33498
    | (have j0 := eq33498 X0 X1
       grind)
    | exact resolve eq33498 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33498
  have eq33722 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33548 X0 X1
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq33548
    | (have j0 := eq33548 X0 X1
       grind)
    | exact resolve eq33548 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33548
  have eq33935 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33722 X0 (M.op X0 X1)
       have i₂ := eq17439 X0 X1
       grind)
    | exact superpose eq17439 eq33722
    | (have j1 := eq17439 X0 X1
       grind)
    | (have r₁ := eq33722 X1 X1
       have r₂ := eq17439 X1 X1
       grind)
    | (have r₁ := eq33722 X0 X1
       have r₂ := eq17439 (M.op X1 (M.op X0 X1)) X1
       grind)
    | (have r₁ := eq33722 X0 X0
       have r₂ := eq17439 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq33722 eq17439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33722
  have eq34001 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33935 X0 X1
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq33935
    | (have j0 := eq33935 X0 X1
       grind)
    | (have r₁ := eq33935 X1 X1
       have r₂ := eq509 X1 X1
       grind)
    | exact resolve eq33935 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33935
  have eq34002 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34001 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34001
  have eq34014 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34002 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq34002
    | (have j0 := eq34002 X0 X1
       grind)
    | exact resolve eq34002 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34002
  have eq34169 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op (M.op X2 X1) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq666 X0 X1 X2
       have i₂ := eq33536 X1 X0
       grind)
    | exact superpose eq33536 eq666
    | (have j1 := eq33536 X1 X0
       grind)
    | (have r₁ := eq666 X0 X0 X0
       have r₂ := eq33536 X0 (M.op X0 X0)
       grind)
    | exact resolve eq666 eq33536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34190 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq33536 X1 X0
       grind)
    | exact superpose eq33536 eq9
    | (have j1 := eq33536 X1 X0
       grind)
    | exact resolve eq9 eq33536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34581 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X1 (M.op X0 X0)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34190 (M.op X0 X0) X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq34190
    | (have j0 := eq34190 (M.op X0 X0) X1
       grind)
    | exact resolve eq34190 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34190
  have eq35978 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ (M.op X1 X1) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X1 X2 (M.op X0 X0)
       have i₂ := eq34581 X1 X0
       grind)
    | exact superpose eq34581 eq85
    | (have j1 := eq34581 X1 X0
       grind)
    | exact resolve eq85 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq35979 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 (M.op X1 X1)) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 (M.op X1 X1)
       have i₂ := eq34581 X0 X1
       grind)
    | exact superpose eq34581 eq770
    | (have j1 := eq34581 X1 X0
       grind)
    | exact resolve eq770 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35981 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op X1 X0)) = X0 ∨ (M.op X0 (M.op X1 X1)) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2100 X0 (M.op X1 X1) X2
       have i₂ := eq34581 X0 X1
       grind)
    | exact superpose eq34581 eq2100
    | (have j1 := eq34581 X1 X0
       grind)
    | exact resolve eq2100 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq36301 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35981 X0 X1 x
       have i₂ := eq4600 X1 X0 X0 x
       grind)
    | exact superpose eq4600 eq35981
    | (have j0 := eq35981 X0 X1 x
       grind)
    | exact resolve eq35981 eq4600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600 eq35981
  have eq36303 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35979 X0 X1
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq35979
    | (have j0 := eq35979 X0 X1
       grind)
    | exact resolve eq35979 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35979
  have eq36395 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36301 X1 (M.op X0 X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq36301
    | (have j0 := eq36301 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq36301 (M.op X1 X0) X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq36301 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36798 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) ≠ (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35978 X0 (M.op X0 X0) X2
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq35978
    | (have r₁ := eq35978 (M.op X1 X0) X0 X2
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq35978 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35978
  have eq37114 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) X0)) = X0 ∨ (M.op X1 X1) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X1 X0
       have i₂ := eq36395 X1 X0
       grind)
    | exact superpose eq36395 eq770
    | (have j1 := eq36395 X1 X0
       grind)
    | exact resolve eq770 eq36395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36395
  have eq37616 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36798 X1 (M.op X0 X0) X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq36798
    | (have j0 := eq36798 X1 (M.op X0 X0) x
       grind)
    | exact resolve eq36798 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38285 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37114 X0 (M.op X0 X0)
       have i₂ := eq36798 X0 X0 X0
       grind)
    | exact superpose eq36798 eq37114
    | (have j0 := eq37114 X0 X0
       have j1 := eq36798 X0 X0 x
       grind)
    | exact resolve eq37114 eq36798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38539 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 ∨ (M.op X1 X1) ≠ (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq795 X0 X1 (M.op (M.op X1 X1) X0)
       have i₂ := eq37114 X0 X1
       grind)
    | exact superpose eq37114 eq795
    | (have j1 := eq37114 X0 X1
       grind)
    | exact resolve eq795 eq37114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37114
  have eq38664 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X0)) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq38285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38285
  have eq38877 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37616 X0 (M.op X0 X0)
       have i₂ := eq36798 X0 X0 X0
       grind)
    | exact superpose eq36798 eq37616
    | (have j1 := eq36798 X0 X0 x
       grind)
    | exact resolve eq37616 eq36798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39013 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38877 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38877
  have eq40365 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X0 ∨ (M.op X0 (M.op X2 X2)) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416 X1 X2 X0 X2
       have i₂ := eq38664 X2 X0
       grind)
    | exact superpose eq38664 eq416
    | (have j1 := eq38664 X2 X0
       grind)
    | exact resolve eq416 eq38664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq40381 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2071 X0 X1 X1
       have i₂ := eq38664 X1 (M.op X0 X0)
       grind)
    | exact superpose eq38664 eq2071
    | (have j1 := eq38664 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq2071 X1 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq38664 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq2071 eq38664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071 eq38664
  have eq40746 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (M.op X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40381 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq40381
    | (have j0 := eq40381 X0 X1
       grind)
    | (have r₁ := eq40381 X0 (M.op X0 X0)
       have r₂ := eq75 (M.op X0 X0)
       grind)
    | exact resolve eq40381 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40381
  have eq63298 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 (M.op X1 X1)) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34014 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq34581 X0 X1
       grind)
    | exact superpose eq34581 eq34014
    | (have j0 := eq34014 (M.op X1 X1) (M.op (M.op X0 X0) X0)
       have j1 := eq34581 X1 X0
       grind)
    | (have r₁ := eq34014 (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq34581 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq34014 X0 X0
       have r₂ := eq34581 X0 X0
       grind)
    | (have r₁ := eq34014 (M.op X1 (M.op X0 X0)) X0
       have r₂ := eq34581 X0 X1
       grind)
    | exact resolve eq34014 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34581
  have eq63366 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = X0 ∨ (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34014 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq697 X0 X1
       grind)
    | exact superpose eq697 eq34014
    | (have j0 := eq34014 X0 X1
       grind)
    | (have r₁ := eq34014 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq697 X0 X0
       grind)
    | exact resolve eq34014 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34014
  have eq63428 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63366 X0 X1
       have i₂ := eq436 X0 X1 X0 X1
       grind)
    | exact superpose eq436 eq63366
    | (have j0 := eq63366 X0 X1
       grind)
    | exact resolve eq63366 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq63366
  have eq63489 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 (M.op X1 X1)) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63298 X0 X1
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq63298
    | (have j0 := eq63298 X0 X1
       grind)
    | (have r₁ := eq63298 X0 X0
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq63298 (M.op (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1))) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) X1
       have r₂ := eq77 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq63298 (M.op X1 X0) X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq63298 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63298
  have eq63527 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63428 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq63428
    | (have j0 := eq63428 X0 X1
       grind)
    | exact resolve eq63428 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63428
  have eq63528 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63527
  have eq63587 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 (M.op X1 X1)) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63489 X0 X1
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq63489
    | (have j0 := eq63489 X0 X1
       grind)
    | (have r₁ := eq63489 (M.op X0 X0) (M.op (M.op X1 X0) X0)
       have r₂ := eq100 X0 X1
       grind)
    | (have r₁ := eq63489 (M.op (M.op X1 X0) X0) (M.op X0 X0)
       have r₂ := eq100 X0 X1
       grind)
    | exact resolve eq63489 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63489
  have eq63588 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63587 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63587
  have eq78152 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63588 X1 (M.op X0 X1)
       have i₂ := eq1496 X0 X1 X0
       grind)
    | exact superpose eq1496 eq63588
    | (have j0 := eq63588 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq63588 X1 (M.op X0 X1)
       have r₂ := eq1496 X0 X1 X0
       grind)
    | (have r₁ := eq63588 (M.op X0 X1) (M.op X1 (M.op (M.op x X1) (M.op X0 X1)))
       have r₂ := eq1496 X0 X1 x
       grind)
    | (have r₁ := eq63588 (M.op X1 (M.op (M.op x X1) (M.op X0 X1))) (M.op X0 X1)
       have r₂ := eq1496 X0 X1 x
       grind)
    | exact resolve eq63588 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq78156 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63588 X0 (M.op X0 X1)
       have i₂ := eq2411 X0 X1 X0
       grind)
    | exact superpose eq2411 eq63588
    | (have j0 := eq63588 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq63588 X0 (M.op X0 X1)
       have r₂ := eq2411 X0 X1 X0
       grind)
    | (have r₁ := eq63588 (M.op X0 X1) (M.op X0 (M.op (M.op x X1) (M.op X0 X1)))
       have r₂ := eq2411 X0 X1 x
       grind)
    | (have r₁ := eq63588 (M.op X0 (M.op (M.op x X1) (M.op X0 X1))) (M.op X0 X1)
       have r₂ := eq2411 X0 X1 x
       grind)
    | exact resolve eq63588 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411 eq63588
  have eq78184 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78156
  have eq78188 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78152
  have eq78225 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78184 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq78184
    | (have j0 := eq78184 X0 X1
       grind)
    | exact resolve eq78184 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78184
  have eq78228 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78188 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq78188
    | (have j0 := eq78188 X0 X1
       grind)
    | exact resolve eq78188 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78188
  have eq79577 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X1 X0)))) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1293 X0 X0
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq1293
    | (have j1 := eq78225 X1 X0
       grind)
    | exact resolve eq1293 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79850 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 X0) (M.op X0 X1)) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq666 X1 X0 X2
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq666
    | (have j1 := eq78225 X0 X1
       grind)
    | exact resolve eq666 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq79862 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1293 X1 X0
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq1293
    | (have j1 := eq78225 X0 X1
       grind)
    | exact resolve eq1293 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79900 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X1 X0 X1
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq871
    | (have j1 := eq78225 X0 X1
       grind)
    | exact resolve eq871 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq79933 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23915 X1 X0 X1
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq23915
    | (have j1 := eq78225 X0 X1
       grind)
    | exact resolve eq23915 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79968 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) X1)) ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 X1
       have i₂ := eq78225 (M.op X0 X0) X1
       grind)
    | exact superpose eq78225 eq770
    | (have j1 := eq78225 (M.op X0 X0) X1
       grind)
    | exact resolve eq770 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq80006 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq509 X1 (M.op X0 X1)
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq509
    | (have j1 := eq78225 X0 X1
       grind)
    | (have r₁ := eq509 X1 X1
       have r₂ := eq78225 (M.op X1 X1) X1
       grind)
    | exact resolve eq509 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80096 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5898 X1 (M.op X0 X1) X2 X3 X4
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq5898
    | (have j1 := eq78225 X0 X1
       grind)
    | exact resolve eq5898 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq80293 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80096 X0 X1 x x x
       have i₂ := eq531 X0 x x X1 x
       grind)
    | exact superpose eq531 eq80096
    | (have j0 := eq80096 X0 X1 x x x
       grind)
    | exact resolve eq80096 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq80096
  have eq80361 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79968 X0 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq79968
    | (have j0 := eq79968 X0 X1
       grind)
    | exact resolve eq79968 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79968
  have eq80365 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79933 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq79933
    | (have j0 := eq79933 X0 X1
       grind)
    | (have r₁ := eq79933 X0 (M.op X0 X0)
       have r₂ := eq75 X0
       grind)
    | exact resolve eq79933 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79933
  have eq80455 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79577 X0 X1
       have i₂ := eq697 X0 X1
       grind)
    | exact superpose eq697 eq79577
    | (have j0 := eq79577 X0 X1
       grind)
    | exact resolve eq79577 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq79577
  have eq81307 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36301 X1 X0
       have i₂ := eq80365 X0 X1
       grind)
    | exact superpose eq80365 eq36301
    | (have j0 := eq36301 X1 X0
       have j1 := eq80365 X0 X1
       grind)
    | (have r₁ := eq36301 X1 X0
       have r₂ := eq80365 X0 X1
       grind)
    | (have r₁ := eq36301 X0 X1
       have r₂ := eq80365 X0 (M.op X1 X0)
       grind)
    | exact resolve eq36301 eq80365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81523 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq795 X0 X1 (M.op X0 X0)
       have i₂ := eq80365 X0 X1
       grind)
    | exact superpose eq80365 eq795
    | (have j1 := eq80365 X0 X1
       grind)
    | exact resolve eq795 eq80365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq81731 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X0)) = X0 ∨ (M.op X0 (M.op X1 X1)) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5139 X0 (M.op X0 X0) X2
       have i₂ := eq80365 X0 (M.op X0 X0)
       grind)
    | exact superpose eq80365 eq5139
    | (have j1 := eq80365 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq5139 X0 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq80365 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact resolve eq5139 eq80365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139 eq80365
  have eq81760 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq81307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81307
  have eq81768 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X0 ∨ (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81731 X0 X1 x
       have i₂ := eq5529 x X0 X1
       grind)
    | exact superpose eq5529 eq81731
    | (have j0 := eq81731 X0 X1 x
       grind)
    | exact resolve eq81731 eq5529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529 eq81731
  have eq82306 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78225 X1 X0
       have i₂ := eq81760 X1 X0
       grind)
    | exact superpose eq81760 eq78225
    | (have j0 := eq78225 X1 X0
       have j1 := eq81760 X1 X0
       grind)
    | (have r₁ := eq78225 X0 (M.op X0 X0)
       have r₂ := eq81760 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq78225 X1 (M.op X0 X1)
       have r₂ := eq81760 X0 X1
       grind)
    | exact resolve eq78225 eq81760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82339 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1418 X0 X0 X1 X1
       have i₂ := eq81760 X0 X1
       grind)
    | exact superpose eq81760 eq1418
    | (have j1 := eq81760 X1 X0
       grind)
    | exact resolve eq1418 eq81760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq82633 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82306
  have eq82840 : (σ x) ≠ (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq82633 (σ (M.op x x)) (σ x)
       grind)
    | (have r₁ := eq82633 (σ (M.op x x)) (σ x)
       have r₂ := eq14080
       grind)
    | exact resolve eq82633 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080
  have eq83206 : (σ x) ≠ (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq82840
       have i₂ := eq13583 x (M.op x x)
       grind)
    | exact superpose eq13583 eq82840
    | (have j1 := eq13583 x (M.op x x)
       grind)
    | exact resolve eq82840 eq13583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13583
  have eq83479 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X2) (M.op X0 X0)) ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1148 X0 X2 X1
       have i₂ := eq78228 X1 X0
       grind)
    | exact superpose eq78228 eq1148
    | (have j1 := eq78228 X1 X0
       grind)
    | exact resolve eq1148 eq78228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83554 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23915 X1 X0 X1
       have i₂ := eq78228 X0 X1
       grind)
    | exact superpose eq78228 eq23915
    | (have j1 := eq78228 X1 X0
       grind)
    | exact resolve eq23915 eq78228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23915
  have eq83984 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83554 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq83554
    | (have j0 := eq83554 X0 X1
       grind)
    | exact resolve eq83554 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq83554
  have eq84421 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36301 X1 X0
       have i₂ := eq83984 X0 X1
       grind)
    | exact superpose eq83984 eq36301
    | (have j0 := eq36301 X1 X0
       have j1 := eq83984 X0 X1
       grind)
    | (have r₁ := eq36301 X1 X0
       have r₂ := eq83984 X0 X1
       grind)
    | exact resolve eq36301 eq83984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84598 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 X1) X0) ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X1 (M.op X0 X0) X2
       have i₂ := eq83984 X0 X1
       grind)
    | exact superpose eq83984 eq99
    | (have j1 := eq83984 X0 X1
       grind)
    | exact resolve eq99 eq83984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq84796 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40746 X1 X0
       have i₂ := eq83984 X0 (M.op X1 X1)
       grind)
    | exact superpose eq83984 eq40746
    | (have j0 := eq40746 X1 X0
       have j1 := eq83984 X1 X0
       grind)
    | (have r₁ := eq40746 X0 X0
       have r₂ := eq83984 X0 (M.op X0 X0)
       grind)
    | exact resolve eq40746 eq83984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40746
  have eq84797 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op (M.op X1 X1) X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39013 X0 X1
       have i₂ := eq83984 X0 (M.op X1 X1)
       grind)
    | exact superpose eq83984 eq39013
    | (have j0 := eq39013 X0 X1
       have j1 := eq83984 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq39013 X0 X1
       have r₂ := eq83984 X0 (M.op X1 X1)
       grind)
    | exact resolve eq39013 eq83984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39013
  have eq84874 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq84797 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84797
  have eq84875 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) ≠ X0 ∨ (M.op X0 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84796
  have eq84879 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq84421 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84421
  have eq87651 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82633 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq79900 X1 X0
       grind)
    | exact superpose eq79900 eq82633
    | (have j0 := eq82633 X0 X1
       have j1 := eq79900 X1 X0
       grind)
    | (have r₁ := eq82633 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have r₂ := eq79900 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq82633 X1 X1
       have r₂ := eq79900 X1 X1
       grind)
    | (have r₁ := eq82633 (M.op (M.op X1 X1) X1) X1
       have r₂ := eq79900 (M.op X1 X1) X1
       grind)
    | exact resolve eq82633 eq79900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87666 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq87651 X0 X1
       have j1 := eq82633 X0 X1
       grind)
    | (have r₁ := eq87651 X0 X1
       have r₂ := eq82633 X0 X1
       grind)
    | (have r₁ := eq87651 (M.op X1 X1) X1
       have r₂ := eq82633 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq87651 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq82633 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq87651 eq82633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87651
  have eq87795 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87666 X0 X1
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq87666
    | (have j0 := eq87666 X0 X1
       grind)
    | exact resolve eq87666 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87666
  have eq87981 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87795 (M.op X0 X0) X1
       have i₂ := eq79862 X0 X1
       grind)
    | exact superpose eq79862 eq87795
    | (have j0 := eq87795 X1 X0
       have j1 := eq79862 X0 X1
       grind)
    | (have r₁ := eq87795 X1 X1
       have r₂ := eq79862 X1 X1
       grind)
    | (have r₁ := eq87795 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq79862 (M.op X0 X0) X1
       grind)
    | exact resolve eq87795 eq79862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79862
  have eq88042 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) ≠ X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87981 X0 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq87981
    | (have j0 := eq87981 X0 X1
       grind)
    | exact resolve eq87981 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87981
  have eq88927 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63528 X1 X1
       have i₂ := eq80006 X0 X1
       grind)
    | (have i₁ := eq63528 (M.op X0 X0) X1
       have i₂ := eq80006 X0 X1
       grind)
    | exact superpose eq80006 eq63528
    | (have j1 := eq80006 X0 X1
       grind)
    | (have r₁ := eq63528 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq80006 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq63528 X0 X0
       have r₂ := eq80006 X0 (M.op X0 X0)
       grind)
    | exact resolve eq63528 eq80006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63528
  have eq89127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37616 X1 X0
       have i₂ := eq80006 X1 X0
       grind)
    | (have i₁ := eq37616 X0 (M.op X0 X0)
       have i₂ := eq80006 X0 (M.op X0 X0)
       grind)
    | exact superpose eq80006 eq37616
    | (have j0 := eq37616 X1 X0
       have j1 := eq80006 X1 X0
       grind)
    | (have r₁ := eq37616 X0 X1
       have r₂ := eq80006 X0 X1
       grind)
    | (have r₁ := eq37616 X0 (M.op X0 X0)
       have r₂ := eq80006 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq37616 X0 X0
       have r₂ := eq80006 X0 (M.op X0 X0)
       grind)
    | exact resolve eq37616 eq80006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37616 eq80006
  have eq89506 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq89127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89127
  have eq89511 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq88927 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88927
  have eq89873 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36301 X1 X0
       have i₂ := eq89506 X0 X1
       grind)
    | exact superpose eq89506 eq36301
    | (have j0 := eq36301 X1 X0
       have j1 := eq89506 X0 X1
       grind)
    | (have r₁ := eq36301 X1 X0
       have r₂ := eq89506 X0 X1
       grind)
    | (have r₁ := eq36301 X1 X1
       have r₂ := eq89506 (M.op X1 X1) X1
       grind)
    | exact resolve eq36301 eq89506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36301 eq89506
  have eq90343 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq89873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89873
  have eq90712 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17475 X0 X1
       have i₂ := eq90343 X1 X0
       grind)
    | exact superpose eq90343 eq17475
    | (have j0 := eq17475 X0 X1
       have j1 := eq90343 X1 X0
       grind)
    | (have r₁ := eq17475 X1 X1
       have r₂ := eq90343 X1 X1
       grind)
    | exact resolve eq17475 eq90343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17475 eq90343
  have eq91413 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80293 X1 (M.op X0 X0)
       have i₂ := eq83984 X0 X1
       grind)
    | exact superpose eq83984 eq80293
    | (have j1 := eq83984 X1 X0
       grind)
    | (have r₁ := eq80293 X0 (M.op X0 X0)
       have r₂ := eq83984 X0 X0
       grind)
    | exact resolve eq80293 eq83984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80293 eq83984
  have eq119397 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81768 X1 X0
       have i₂ := eq91413 X1 X0
       grind)
    | exact superpose eq91413 eq81768
    | (have j0 := eq81768 X1 X0
       have j1 := eq91413 X0 X1
       grind)
    | (have r₁ := eq81768 X1 X1
       have r₂ := eq91413 X1 X1
       grind)
    | (have r₁ := eq81768 X1 X1
       have r₂ := eq91413 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq81768 X0 X1
       have r₂ := eq91413 X0 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq81768 eq91413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81768
  have eq119813 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88042 X0 (M.op X1 X1)
       have i₂ := eq91413 X0 X1
       grind)
    | exact superpose eq91413 eq88042
    | (have j0 := eq88042 X0 X0
       have j1 := eq91413 X0 X1
       grind)
    | (have r₁ := eq88042 X1 (M.op X1 X1)
       have r₂ := eq91413 X1 X1
       grind)
    | (have r₁ := eq88042 X0 X1
       have r₂ := eq91413 X0 X1
       grind)
    | (have r₁ := eq88042 X1 X0
       have r₂ := eq91413 X0 X1
       grind)
    | exact resolve eq88042 eq91413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88042
  have eq119930 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq119813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119813
  have eq119948 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq119397 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119397
  have eq121927 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) ≠ X0 ∨ X0 ≠ X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78228 X1 X0
       have i₂ := eq119948 X1 X0
       grind)
    | exact superpose eq119948 eq78228
    | (have j0 := eq78228 X1 X0
       have j1 := eq119948 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq78228 X0 X1
       have r₂ := eq119948 (M.op X1 X1) (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq78228 X0 X1
       have r₂ := eq119948 (M.op X1 (M.op X0 X1)) (M.op X1 X1)
       grind)
    | (have r₁ := eq78228 X0 X0
       have r₂ := eq119948 X0 (M.op X0 X0)
       grind)
    | exact resolve eq78228 eq119948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119948
  have eq122341 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ X0 ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq121927 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121927
  have eq127158 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X2 (M.op X1 X1)) X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79850 (M.op X0 X0) (M.op X1 X1) X2
       have i₂ := eq79900 X0 X1
       grind)
    | exact superpose eq79900 eq79850
    | (have j0 := eq79850 X1 X0 X2
       have j1 := eq79900 X1 X0
       grind)
    | (have r₁ := eq79850 X0 X1 X0
       have r₂ := eq79900 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq79850 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have r₂ := eq79900 X0 (M.op X0 X0)
       grind)
    | exact resolve eq79850 eq79900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79900
  have eq127255 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X1) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79850 X1 (M.op X0 X1) X2
       have i₂ := eq78225 X0 X1
       grind)
    | exact superpose eq78225 eq79850
    | (have j0 := eq79850 X0 X1 X2
       have j1 := eq78225 X0 X1
       grind)
    | (have r₁ := eq79850 X0 X1 X0
       have r₂ := eq78225 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq79850 (M.op X0 X0) (M.op X0 (M.op X0 X0)) X2
       have r₂ := eq78225 X0 (M.op X0 X0)
       grind)
    | exact resolve eq79850 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128334 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X1) (M.op X0 X0)) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq127255 X0 X1 X2
       have j1 := eq82633 X1 X0
       grind)
    | (have r₁ := eq127255 X0 X1 X1
       have r₂ := eq82633 (M.op X0 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq127255 X1 X0 X2
       have r₂ := eq82633 X0 X1
       grind)
    | (have r₁ := eq127255 X0 (M.op X1 X1) X2
       have r₂ := eq82633 (M.op X0 X0) X1
       grind)
    | exact resolve eq127255 eq82633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127255
  have eq128418 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X2 (M.op X1 X1)) X0) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq127158 X0 X1 X2
       have j1 := eq82633 X0 X1
       grind)
    | (have r₁ := eq127158 X0 X1 (M.op X1 X1)
       have r₂ := eq82633 X0 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | (have r₁ := eq127158 X0 X1 X2
       have r₂ := eq82633 X0 X1
       grind)
    | (have r₁ := eq127158 (M.op X1 X1) X1 X2
       have r₂ := eq82633 (M.op X1 X1) X1
       grind)
    | exact resolve eq127158 eq82633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127158
  have eq128689 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) X0) = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128418 X0 X1 X2
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq128418
    | (have j0 := eq128418 X0 X1 X2
       grind)
    | exact resolve eq128418 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128418
  have eq129161 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X2 (M.op (M.op X2 X2) X0)) ≠ X2 ∨ (M.op X2 X2) ≠ (M.op (M.op X2 X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq128689 (M.op (M.op X2 X2) X0) X2 x
       have i₂ := eq82339 X0 (M.op X2 X2) x
       grind)
    | exact superpose eq82339 eq128689
    | (have j0 := eq128689 (M.op (M.op X2 X2) X0) X2 X2
       have j1 := eq82339 (M.op (M.op X2 X2) X0) X2 X2
       grind)
    | (have r₁ := eq128689 (M.op x (M.op X2 x)) (M.op X2 x) X2
       have r₂ := eq82339 (M.op X2 x) x X2
       grind)
    | exact resolve eq128689 eq82339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82339
  have eq129415 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X2))) ≠ X0 ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1148 X2 (M.op X0 X0) X1
       have i₂ := eq128689 (M.op X2 (M.op X1 X2)) X0 X2
       grind)
    | exact superpose eq128689 eq1148
    | (have j1 := eq128689 (M.op X2 (M.op X1 X2)) X0 X2
       grind)
    | (have r₁ := eq1148 X2 X2 X2
       have r₂ := eq128689 (M.op X2 (M.op X2 X2)) (M.op X2 X2) X2
       grind)
    | exact resolve eq1148 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129610 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) (M.op X2 X0)) = X0 ∨ (M.op X0 X2) ≠ X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1148 X0 x (M.op X2 (M.op x x))
       have i₂ := eq128689 X0 x X2
       grind)
    | exact superpose eq128689 eq1148
    | (have j1 := eq128689 X2 X0 X2
       grind)
    | (have r₁ := eq1148 X2 X2 X2
       have r₂ := eq128689 (M.op X2 (M.op X2 X2)) (M.op X2 X2) X2
       grind)
    | exact resolve eq1148 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq129614 : ∀ X0 X2 : G, (M.op X2 (M.op X2 X0)) = X0 ∨ (M.op X0 X2) ≠ X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1293 X0 (M.op X2 (M.op x x))
       have i₂ := eq128689 X0 x X2
       grind)
    | exact superpose eq128689 eq1293
    | (have j1 := eq128689 X2 X0 X2
       grind)
    | exact resolve eq1293 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129695 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12076 X0 (M.op x (M.op X1 X1))
       have i₂ := eq128689 X0 X1 x
       grind)
    | exact superpose eq128689 eq12076
    | (have j1 := eq128689 X1 X0 x
       grind)
    | (have r₁ := eq12076 X1 X1
       have r₂ := eq128689 X1 X1 x
       grind)
    | exact resolve eq12076 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq129717 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33536 (M.op x (M.op X1 X1)) X0
       have i₂ := eq128689 X0 X1 x
       grind)
    | exact superpose eq128689 eq33536
    | (have j1 := eq128689 X1 X0 x
       grind)
    | (have r₁ := eq33536 X0 X1
       have r₂ := eq128689 (M.op X0 X1) X1 x
       grind)
    | (have r₁ := eq33536 (M.op x (M.op (M.op X0 X0) (M.op X0 X0))) X0
       have r₂ := eq128689 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq33536 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33536
  have eq129737 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78228 (M.op x (M.op X1 X1)) X0
       have i₂ := eq128689 X0 X1 x
       grind)
    | exact superpose eq128689 eq78228
    | (have j1 := eq128689 X1 X0 x
       grind)
    | (have r₁ := eq78228 (M.op x (M.op X1 X1)) X1
       have r₂ := eq128689 X1 X1 x
       grind)
    | exact resolve eq78228 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78228
  have eq129866 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X3)) ≠ X0 ∨ (M.op X3 (M.op X2 X0)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1416 X0 (M.op X2 (M.op x x)) X2
       have i₂ := eq128689 (M.op X2 X0) x X2
       grind)
    | exact superpose eq128689 eq1416
    | (have j1 := eq128689 (M.op X2 X3) X0 X2
       grind)
    | exact resolve eq1416 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq129883 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 X0))) X0)) = X0 ∨ (M.op X0 (M.op X2 X3)) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7574 X0 (M.op X2 (M.op X1 X1)) X2 X3
       have i₂ := eq128689 (M.op X2 X0) X1 X2
       grind)
    | exact superpose eq128689 eq7574
    | (have j1 := eq128689 (M.op X2 X3) X0 X2
       grind)
    | exact resolve eq7574 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7574
  have eq129888 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X3)) ≠ X0 ∨ (M.op X3 (M.op X3 X0)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq8373 (M.op X2 (M.op x x)) x X2
       have i₂ := eq128689 (M.op x X2) x X2
       grind)
    | exact superpose eq128689 eq8373
    | (have j1 := eq128689 (M.op X2 X3) X0 X2
       grind)
    | exact resolve eq8373 eq128689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373 eq128689
  have eq130031 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X3)) ≠ X0 ∨ (M.op X3 (M.op X0 X0)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq129883 X0 x X2 X3 x
       have i₂ := eq433 X0 x X0 x
       grind)
    | exact superpose eq433 eq129883
    | (have j0 := eq129883 X0 x X2 X3 x
       grind)
    | exact resolve eq129883 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq129883
  have eq130090 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq129717 X0 X1
       have j1 := eq87795 X1 X0
       grind)
    | (have r₁ := eq129717 X0 X1
       have r₂ := eq87795 X0 X1
       grind)
    | (have r₁ := eq129717 X1 X0
       have r₂ := eq87795 X0 X1
       grind)
    | (have r₁ := eq129717 (M.op X0 X0) X1
       have r₂ := eq87795 X0 (M.op X1 X1)
       grind)
    | exact resolve eq129717 eq87795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129717
  have eq130259 : ∀ X0 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X2 X2) X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq129161 X0 X2
       have j1 := eq80361 X2 X0
       grind)
    | (have r₁ := eq129161 (M.op X0 X0) (M.op (M.op X0 X0) x)
       have r₂ := eq80361 X0 x
       grind)
    | (have r₁ := eq129161 (M.op (M.op X0 X0) x) (M.op X0 X0)
       have r₂ := eq80361 X0 x
       grind)
    | (have r₁ := eq129161 x X0
       have r₂ := eq80361 X0 x
       grind)
    | exact resolve eq129161 eq80361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80361 eq129161
  have eq130396 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq130090 (M.op X0 X1) X0
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq130090
    | (have j0 := eq130090 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq130090 (M.op X0 X0) X0
       have r₂ := eq509 X0 X0
       grind)
    | exact resolve eq130090 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130090
  have eq131574 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87795 (M.op X1 X0) X1
       have i₂ := eq129614 X0 X1
       grind)
    | exact superpose eq129614 eq87795
    | (have j0 := eq87795 X1 X0
       have j1 := eq129614 X0 X1
       grind)
    | (have r₁ := eq87795 (M.op X0 X0) X0
       have r₂ := eq129614 X0 X0
       grind)
    | (have r₁ := eq87795 x x
       have r₂ := eq129614 x x
       grind)
    | (have r₁ := eq87795 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq129614 (M.op X0 X0) x
       grind)
    | exact resolve eq87795 eq129614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129614
  have eq131680 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq131574 X0 X1
       have i₂ := eq3544 X1 X0 X1
       grind)
    | exact superpose eq3544 eq131574
    | (have j0 := eq131574 X0 X1
       grind)
    | (have r₁ := eq131574 (M.op (M.op X0 X1) (M.op x X1)) (M.op X1 (M.op x X1))
       have r₂ := eq3544 X0 X1 x
       grind)
    | (have r₁ := eq131574 (M.op X1 (M.op x X1)) (M.op (M.op X0 X1) (M.op x X1))
       have r₂ := eq3544 X0 X1 x
       grind)
    | exact resolve eq131574 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131574
  have eq132401 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq130259 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq130259
    | (have j0 := eq130259 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq130259 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132622 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq132401 X0 X1
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq132401
    | (have j0 := eq132401 X0 X1
       grind)
    | exact resolve eq132401 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132401
  have eq133536 : ∀ X0 X1 X2 : G, (M.op X2 X0) ≠ X2 ∨ (M.op X2 X0) = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129415 X1 X2 X0
       have i₂ := eq81760 X2 X0
       grind)
    | exact superpose eq81760 eq129415
    | (have j0 := eq129415 X1 X2 X0
       have j1 := eq81760 X2 X0
       grind)
    | (have r₁ := eq129415 (M.op X1 X0) X1 X0
       have r₂ := eq81760 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq129415 X0 X0 X1
       have r₂ := eq81760 X0 X1
       grind)
    | (have r₁ := eq129415 (M.op (M.op X1 X2) X1) X1 X2
       have r₂ := eq81760 (M.op X1 X2) X1
       grind)
    | exact resolve eq129415 eq81760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81760 eq129415
  have eq144206 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq130031 X0 X0 X1
       have i₂ := eq130396 X0 X1
       grind)
    | exact superpose eq130396 eq130031
    | (have j0 := eq130031 X0 x X1
       have j1 := eq130396 X0 X1
       grind)
    | (have r₁ := eq130031 X0 X0 X1
       have r₂ := eq130396 X0 X1
       grind)
    | (have r₁ := eq130031 (M.op X0 X0) x X0
       have r₂ := eq130396 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq130031 eq130396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130031 eq130396
  have eq144618 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq144206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144206
  have eq148344 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X1 X1) X0) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132622 (M.op X1 X1) X0
       have i₂ := eq89511 X1 X0
       grind)
    | exact superpose eq89511 eq132622
    | (have j0 := eq132622 (M.op X1 X1) X0
       have j1 := eq89511 X1 X0
       grind)
    | (have r₁ := eq132622 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq89511 X0 (M.op X0 X0)
       grind)
    | exact resolve eq132622 eq89511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89511 eq132622
  have eq148374 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X1 X1) X0) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq148344 X0 X1
       have j1 := eq82633 X0 X1
       grind)
    | (have r₁ := eq148344 X0 X1
       have r₂ := eq82633 X0 X1
       grind)
    | (have r₁ := eq148344 (M.op X1 X1) X1
       have r₂ := eq82633 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq148344 X0 X0
       have r₂ := eq82633 X0 X0
       grind)
    | exact resolve eq148344 eq82633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148344
  have eq148531 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148374 X0 X1
       have i₂ := eq77 X1 X1
       grind)
    | exact superpose eq77 eq148374
    | (have j0 := eq148374 X0 X1
       grind)
    | exact resolve eq148374 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148374
  have eq149028 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq130259 X1 X0
       have i₂ := eq148531 X1 X0
       grind)
    | exact superpose eq148531 eq130259
    | (have j0 := eq130259 X0 X1
       have j1 := eq148531 X1 X0
       grind)
    | (have r₁ := eq130259 (M.op X1 X0) X1
       have r₂ := eq148531 X0 X1
       grind)
    | (have r₁ := eq130259 X1 (M.op X1 X0)
       have r₂ := eq148531 X0 X1
       grind)
    | exact resolve eq130259 eq148531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130259
  have eq149094 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40365 X1 X0 X0
       have i₂ := eq148531 (M.op X0 X1) X0
       grind)
    | exact superpose eq148531 eq40365
    | (have j0 := eq40365 X1 X1 X0
       have j1 := eq148531 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq40365 (M.op X1 x) X1 x
       have r₂ := eq148531 (M.op x (M.op X1 x)) (M.op X1 x)
       grind)
    | (have r₁ := eq40365 (M.op X1 X1) X1 X1
       have r₂ := eq148531 (M.op X1 X1) X1
       grind)
    | exact resolve eq40365 eq148531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40365
  have eq149512 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq122341 X1 (M.op X0 X0)
       have i₂ := eq148531 X1 X0
       grind)
    | exact superpose eq148531 eq122341
    | (have j0 := eq122341 X1 X0
       have j1 := eq148531 X1 X0
       grind)
    | (have r₁ := eq122341 X1 (M.op X1 X1)
       have r₂ := eq148531 X1 X1
       grind)
    | (have r₁ := eq122341 X0 X1
       have r₂ := eq148531 X0 X0
       grind)
    | (have r₁ := eq122341 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq148531 X0 X1
       grind)
    | exact resolve eq122341 eq148531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148531
  have eq149839 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ X0 ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq149512 X0 X1
       have j1 := eq82633 X1 X0
       grind)
    | (have r₁ := eq149512 (M.op X1 X1) X0
       have r₂ := eq82633 X0 X1
       grind)
    | (have r₁ := eq149512 X0 (M.op X1 X1)
       have r₂ := eq82633 X0 X1
       grind)
    | (have r₁ := eq149512 X0 X0
       have r₂ := eq82633 X0 X0
       grind)
    | exact resolve eq149512 eq82633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82633 eq149512
  have eq149918 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq149094 X0 X1
       have j1 := eq129866 X0 X0 X1
       grind)
    | (have r₁ := eq149094 (M.op X0 (M.op x x)) X0
       have r₂ := eq129866 X0 x x
       grind)
    | (have r₁ := eq149094 X0 (M.op X0 (M.op x x))
       have r₂ := eq129866 X0 x x
       grind)
    | (have r₁ := eq149094 X0 x
       have r₂ := eq129866 X0 X0 x
       grind)
    | exact resolve eq149094 eq129866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129866 eq149094
  have eq150213 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ (k X0 X1))) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq149918 (τ X0) (τ X1)
       have i₂ := eq13592 X0 X1
       grind)
    | exact superpose eq13592 eq149918
    | (have j0 := eq149918 (τ X0) (τ X1)
       have j1 := eq13592 X0 X1
       grind)
    | exact resolve eq149918 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150241 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149918 X0 X1
       have i₂ := eq17439 X0 X1
       grind)
    | exact superpose eq17439 eq149918
    | (have j0 := eq149918 X0 X1
       have j1 := eq17439 X0 X1
       grind)
    | (have r₁ := eq149918 X0 X1
       have r₂ := eq17439 X0 X1
       grind)
    | (have r₁ := eq149918 X1 X1
       have r₂ := eq17439 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq149918 X0 X1
       have r₂ := eq17439 X0 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq149918 eq17439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17439
  have eq150263 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq150241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150241
  have eq150264 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq150263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150263
  have eq150267 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ (k X0 X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150213
  have eq150575 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op X2 X1) X0) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq150264 X1 (M.op (M.op X2 X1) X0)
       have i₂ := eq81523 X0 X1 X2
       grind)
    | exact superpose eq81523 eq150264
    | (have j0 := eq150264 (M.op (M.op X2 X1) X0) X1
       have j1 := eq81523 X0 X1 X2
       grind)
    | (have r₁ := eq150264 X1 (M.op (M.op X2 X1) (M.op X1 X1))
       have r₂ := eq81523 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq150264 (M.op X0 X1) X0
       have r₂ := eq81523 X0 X1 X2
       grind)
    | (have r₁ := eq150264 X0 (M.op X0 X1)
       have r₂ := eq81523 X0 X1 X2
       grind)
    | exact resolve eq150264 eq81523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81523
  have eq150590 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150264 (τ X0) (τ X1)
       have i₂ := eq13592 X0 X1
       grind)
    | exact superpose eq13592 eq150264
    | (have j0 := eq150264 (τ X0) (τ X1)
       have j1 := eq13592 X0 X1
       grind)
    | exact resolve eq150264 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13592
  have eq150594 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150590 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150590
  have eq150609 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq150575 X0 X1 X2
       have j1 := eq87795 X1 X0
       grind)
    | (have r₁ := eq150575 X1 X0 X2
       have r₂ := eq87795 X0 X1
       grind)
    | (have r₁ := eq150575 (M.op X0 X0) X1 X2
       have r₂ := eq87795 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq150575 X1 X1 X2
       have r₂ := eq87795 X1 X1
       grind)
    | exact resolve eq150575 eq87795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150575
  have eq153364 : ∀ X0 X2 : G, (M.op X2 (M.op X2 X0)) = X0 ∨ (M.op X2 X0) ≠ X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1293 X0 (M.op X2 x)
       have i₂ := eq150609 X0 x X2
       grind)
    | exact superpose eq150609 eq1293
    | (have j1 := eq150609 X2 X0 X2
       grind)
    | exact resolve eq1293 eq150609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq150609
  have eq155292 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149028 X1 (M.op X0 X0)
       have i₂ := eq91413 X1 X0
       grind)
    | exact superpose eq91413 eq149028
    | (have j0 := eq149028 X1 X1
       have j1 := eq91413 X0 X1
       grind)
    | (have r₁ := eq149028 X1 (M.op X1 X1)
       have r₂ := eq91413 X1 X1
       grind)
    | (have r₁ := eq149028 X0 X1
       have r₂ := eq91413 X0 X1
       grind)
    | (have r₁ := eq149028 X1 X0
       have r₂ := eq91413 X0 X1
       grind)
    | exact resolve eq149028 eq91413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149028
  have eq155332 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq155292 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155292
  have eq155358 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq155332 X0 X1
       have j1 := eq122341 X1 X0
       grind)
    | (have r₁ := eq155332 (M.op X0 X0) X0
       have r₂ := eq122341 X0 X1
       grind)
    | (have r₁ := eq155332 X0 (M.op X0 X0)
       have r₂ := eq122341 X0 X1
       grind)
    | (have r₁ := eq155332 X0 X0
       have r₂ := eq122341 X0 X0
       grind)
    | exact resolve eq155332 eq122341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122341 eq155332
  have eq155964 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149839 X1 (M.op X0 X0)
       have i₂ := eq91413 X1 X0
       grind)
    | exact superpose eq91413 eq149839
    | (have j0 := eq149839 X1 (M.op X0 X0)
       have j1 := eq91413 X0 X1
       grind)
    | (have r₁ := eq149839 X1 (M.op X1 X1)
       have r₂ := eq91413 X1 X1
       grind)
    | (have r₁ := eq149839 X0 X1
       have r₂ := eq91413 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq149839 X0 X0
       have r₂ := eq91413 X0 (M.op X0 X0)
       grind)
    | exact resolve eq149839 eq91413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149839
  have eq156002 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq155964 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155964
  have eq156048 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq156002 X0 X1
       have j1 := eq155358 X0 X1
       grind)
    | (have r₁ := eq156002 (M.op X0 X0) X1
       have r₂ := eq155358 X0 X1
       grind)
    | (have r₁ := eq156002 X1 (M.op X0 X0)
       have r₂ := eq155358 X0 X1
       grind)
    | (have r₁ := eq156002 X0 X1
       have r₂ := eq155358 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq156002 eq155358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156002
  have eq156172 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq156048 X0 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq156048
    | (have j0 := eq156048 X0 X1
       grind)
    | (have r₁ := eq156048 (M.op (M.op X1 X0) (M.op X0 X0)) X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq156048 X0 (M.op (M.op X1 X0) (M.op X0 X0))
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq156048 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156048
  have eq157926 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq129888 X1 X0 X0
       have i₂ := eq144618 X0 X1
       grind)
    | exact superpose eq144618 eq129888
    | (have j0 := eq129888 X1 x X0
       have j1 := eq144618 X0 X1
       grind)
    | (have r₁ := eq129888 X0 X0 X0
       have r₂ := eq144618 X0 X0
       grind)
    | (have r₁ := eq129888 (M.op X0 X0) x X0
       have r₂ := eq144618 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq129888 eq144618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129888
  have eq158636 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq157926 X0 X1
       have j1 := eq150264 X0 X1
       grind)
    | (have r₁ := eq157926 X0 X1
       have r₂ := eq150264 X0 X1
       grind)
    | (have r₁ := eq157926 X1 X0
       have r₂ := eq150264 X0 X1
       grind)
    | (have r₁ := eq157926 X0 (M.op X0 X0)
       have r₂ := eq150264 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq157926 eq150264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157926
  have eq186457 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (k X0 X1) ≠ (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq158636 X1 X1
       have i₂ := eq129695 X0 X1
       grind)
    | exact superpose eq129695 eq158636
    | (have j1 := eq129695 X0 X1
       grind)
    | (have r₁ := eq158636 X0 X0
       have r₂ := eq129695 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq158636 X0 X1
       have r₂ := eq129695 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq158636 X0 X1
       have r₂ := eq129695 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq158636 eq129695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129695 eq158636
  have eq186720 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq186457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186457
  have eq187435 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq129737 X1 (M.op X0 X0)
       have i₂ := eq91413 X1 X0
       grind)
    | exact superpose eq91413 eq129737
    | (have j0 := eq129737 X0 X1
       have j1 := eq91413 X0 X1
       grind)
    | (have r₁ := eq129737 X1 (M.op X1 X1)
       have r₂ := eq91413 X1 X1
       grind)
    | (have r₁ := eq129737 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq91413 X0 X1
       grind)
    | (have r₁ := eq129737 X1 (M.op X0 (M.op X1 X1))
       have r₂ := eq91413 X0 X1
       grind)
    | exact resolve eq129737 eq91413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129737
  have eq187476 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq187435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187435
  have eq187528 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq187476 X0 X1
       have j1 := eq155358 X0 X1
       grind)
    | (have r₁ := eq187476 (M.op X0 X0) X1
       have r₂ := eq155358 X0 X1
       grind)
    | (have r₁ := eq187476 X1 (M.op X0 X0)
       have r₂ := eq155358 X0 X1
       grind)
    | (have r₁ := eq187476 X0 X1
       have r₂ := eq155358 X0 X1
       grind)
    | exact resolve eq187476 eq155358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155358 eq187476
  have eq187676 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187528 X0 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq187528
    | (have j0 := eq187528 X0 X1
       grind)
    | (have r₁ := eq187528 (M.op (M.op X1 X0) (M.op X0 X0)) X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq187528 X0 (M.op (M.op X1 X0) (M.op X0 X0))
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq187528 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187528
  have eq189501 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X2 ∨ (M.op X2 (M.op X1 X0)) ≠ X2 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133536 (M.op X0 X1) X1 X1
       have i₂ := eq84879 X0 X1
       grind)
    | exact superpose eq84879 eq133536
    | (have j0 := eq133536 (M.op X1 X0) X2 X2
       have j1 := eq84879 X1 X0
       grind)
    | (have r₁ := eq133536 (M.op X0 X1) X1 X1
       have r₂ := eq84879 X0 X1
       grind)
    | (have r₁ := eq133536 X0 X0 X1
       have r₂ := eq84879 X0 X1
       grind)
    | (have r₁ := eq133536 X0 (M.op X1 (M.op X2 X0)) X2
       have r₂ := eq84879 (M.op X2 X0) X1
       grind)
    | exact resolve eq133536 eq84879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133536
  have eq189559 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X0)) ≠ X2 ∨ X0 = X2 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq189501 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189501
  have eq196567 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78225 (M.op X0 X0) X1
       have i₂ := eq187676 X0 X1
       grind)
    | exact superpose eq187676 eq78225
    | (have j0 := eq78225 X0 X0
       have j1 := eq187676 X0 X1
       grind)
    | (have r₁ := eq78225 X0 X1
       have r₂ := eq187676 (M.op X0 X0) (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq78225 X0 X1
       have r₂ := eq187676 (M.op X1 (M.op X0 X1)) (M.op X0 X0)
       grind)
    | (have r₁ := eq78225 X0 X0
       have r₂ := eq187676 X0 (M.op X0 X0)
       grind)
    | exact resolve eq78225 eq187676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196606 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90712 (M.op X0 X0) X1
       have i₂ := eq187676 X0 X1
       grind)
    | exact superpose eq187676 eq90712
    | (have j0 := eq90712 X0 X0
       have j1 := eq187676 X0 X1
       grind)
    | (have r₁ := eq90712 X1 X1
       have r₂ := eq187676 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq90712 X0 X1
       have r₂ := eq187676 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq90712 X1 X0
       have r₂ := eq187676 X0 X1
       grind)
    | exact resolve eq90712 eq187676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90712 eq187676
  have eq197113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq196606 X0 X1
       have j1 := eq128334 X0 X0 x
       grind)
    | (have r₁ := eq196606 (M.op X0 X0) X1
       have r₂ := eq128334 X0 X0 X0
       grind)
    | (have r₁ := eq196606 X0 (M.op X0 X0)
       have r₂ := eq128334 (M.op X0 X0) (M.op X0 X0) x
       grind)
    | (have r₁ := eq196606 X0 X1
       have r₂ := eq128334 X0 X0 X0
       grind)
    | exact resolve eq196606 eq128334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128334 eq196606
  have eq197123 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq196567 X0 X1
       have j1 := eq156172 X0 X1
       grind)
    | (have r₁ := eq196567 X1 X1
       have r₂ := eq156172 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq196567 X0 X1
       have r₂ := eq156172 (M.op X1 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq196567 X0 X1
       have r₂ := eq156172 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact resolve eq196567 eq156172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196567
  have eq197384 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq197113 X0 X1
       have j1 := eq156172 X0 X1
       grind)
    | (have r₁ := eq197113 X0 X1
       have r₂ := eq156172 X0 X1
       grind)
    | (have r₁ := eq197113 X0 X0
       have r₂ := eq156172 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq197113 X0 X1
       have r₂ := eq156172 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq197113 eq156172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197113
  have eq197391 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq197123 X0 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq197123
    | (have j0 := eq197123 X0 X1
       grind)
    | (have r₁ := eq197123 (M.op (M.op X1 X0) (M.op X0 X0)) X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq197123 X0 (M.op (M.op X1 X0) (M.op X0 X0))
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq197123 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197123
  have eq197684 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op (M.op X0 X0) X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq197391 X1 (M.op X0 X0)
       have i₂ := eq91413 X1 X0
       grind)
    | exact superpose eq91413 eq197391
    | (have j0 := eq197391 X0 X1
       have j1 := eq91413 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq197391 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq91413 X0 X1
       grind)
    | (have r₁ := eq197391 X1 (M.op X0 (M.op X1 X1))
       have r₂ := eq91413 X0 X1
       grind)
    | (have r₁ := eq197391 X1 X1
       have r₂ := eq91413 (M.op X1 X1) X1
       grind)
    | exact resolve eq197391 eq91413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91413 eq197391
  have eq197772 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq197684 X0 X1
       have j1 := eq119930 X0 X1
       grind)
    | (have r₁ := eq197684 X1 X1
       have r₂ := eq119930 X1 X1
       grind)
    | (have r₁ := eq197684 (M.op X0 X0) X1
       have r₂ := eq119930 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq197684 X0 X1
       have r₂ := eq119930 X0 X1
       grind)
    | exact resolve eq197684 eq119930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119930 eq197684
  have eq197855 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq197772 X0 X1
       have j1 := eq156172 X0 X1
       grind)
    | (have r₁ := eq197772 X0 X1
       have r₂ := eq156172 X0 X1
       grind)
    | (have r₁ := eq197772 X0 X1
       have r₂ := eq156172 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq197772 X0 X1
       have r₂ := eq156172 (M.op (M.op X0 X0) X1) X1
       grind)
    | exact resolve eq197772 eq156172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156172 eq197772
  have eq198626 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149918 X1 (M.op X0 X1)
       have i₂ := eq131680 X1 X0
       grind)
    | exact superpose eq131680 eq149918
    | (have j0 := eq149918 (M.op X0 X1) X1
       have j1 := eq131680 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq149918 X1 X1
       have r₂ := eq131680 X1 X1
       grind)
    | (have r₁ := eq149918 X0 X1
       have r₂ := eq131680 X0 X1
       grind)
    | (have r₁ := eq149918 X1 X0
       have r₂ := eq131680 X0 X1
       grind)
    | exact resolve eq149918 eq131680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131680
  have eq198760 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq198626 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198626
  have eq210803 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X2 X2) ≠ (M.op X0 (M.op X2 X2)) ∨ X0 ≠ X2 ∨ (M.op X2 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189559 X0 (M.op X2 X2) X1
       have i₂ := eq197855 X2 X0
       grind)
    | exact superpose eq197855 eq189559
    | (have j0 := eq189559 X0 (M.op X2 X2) X1
       have j1 := eq197855 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq189559 X0 X0 (M.op X0 X0)
       have r₂ := eq197855 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq189559 X0 X1 X1
       have r₂ := eq197855 X0 X1
       grind)
    | (have r₁ := eq189559 X1 X1 X0
       have r₂ := eq197855 X0 X1
       grind)
    | exact resolve eq189559 eq197855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189559 eq197855
  have eq211211 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ X0 ≠ X2 ∨ (M.op X2 X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq210803 X0 X1 X2
       have j1 := eq197384 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq210803 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq197384 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq210803 X0 X1 X2
       have r₂ := eq197384 X0 X1
       grind)
    | (have r₁ := eq210803 X1 X0 X2
       have r₂ := eq197384 X0 X1
       grind)
    | exact resolve eq210803 eq197384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197384 eq210803
  have eq212658 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (k X1 X0) X0) = X0 ∨ (k X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq198760 (k X1 X0) X0
       have i₂ := eq186720 X1 X0
       grind)
    | exact superpose eq186720 eq198760
    | (have j0 := eq198760 (k X1 X0) X0
       have j1 := eq186720 (M.op (k X1 X0) X0) X0
       grind)
    | (have r₁ := eq198760 (k X0 X1) X1
       have r₂ := eq186720 X0 X1
       grind)
    | (have r₁ := eq198760 X0 X1
       have r₂ := eq186720 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq198760 X0 X0
       have r₂ := eq186720 X0 (M.op X0 X0)
       grind)
    | exact resolve eq198760 eq186720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186720 eq198760
  have eq212710 : ∀ X0 X1 : G, (M.op (k X1 X0) X0) = X0 ∨ (k X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq212658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212658
  have eq212774 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq212710 X0 X1
       have j1 := eq211211 X0 X1 (k X1 X0)
       grind)
    | (have r₁ := eq212710 x X1
       have r₂ := eq211211 (M.op (k X1 x) x) X1 x
       grind)
    | (have r₁ := eq212710 X0 X1
       have r₂ := eq211211 X0 X1 (M.op (k X1 X0) X0)
       grind)
    | (have r₁ := eq212710 X0 X1
       have r₂ := eq211211 X0 X1 (k X1 X0)
       grind)
    | exact resolve eq212710 eq211211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211211 eq212710
  have eq217926 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (M.op (τ (σ X0)) (τ (σ (k X0 X1)))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150267 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq150267
    | (have j0 := eq150267 (σ X0) (σ X1)
       grind)
    | exact resolve eq150267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150267
  have eq217967 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (M.op (τ (σ X0)) (k X0 X1)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217926 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq217926
    | (have j0 := eq217926 X0 X1
       grind)
    | exact resolve eq217926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217926
  have eq217980 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) ≠ X0 ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217967 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq217967
    | (have j0 := eq217967 X0 X1
       grind)
    | exact resolve eq217967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217967
  have eq217987 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (M.op X0 (k X0 X1)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq217980 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq217980
    | (have j0 := eq217980 X0 X1
       grind)
    | exact resolve eq217980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217980
  have eq217992 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) ≠ X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq217987 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq217987
    | (have j0 := eq217987 X0 X1
       grind)
    | exact resolve eq217987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217987
  have eq222657 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150594 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq150594
    | (have j0 := eq150594 (σ X0) (σ X1)
       grind)
    | exact resolve eq150594 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150594
  have eq222728 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq222657 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq222657
    | (have j0 := eq222657 X0 X1
       grind)
    | exact resolve eq222657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222657
  have eq222738 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq222728 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq222728
    | (have j0 := eq222728 X0 X1
       grind)
    | exact resolve eq222728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222728
  have eq222745 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq222738 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq222738
    | (have j0 := eq222738 X0 X1
       grind)
    | exact resolve eq222738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222738
  have eq222750 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq222745 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq222745
    | (have j0 := eq222745 X0 X1
       grind)
    | exact resolve eq222745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222745
  have eq222819 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq222750 (M.op X0 X0) X1
       have i₂ := eq36798 X0 X0 X0
       grind)
    | exact superpose eq36798 eq222750
    | (have j0 := eq222750 (M.op X0 X0) X1
       have j1 := eq36798 X0 X0 x
       grind)
    | (have r₁ := eq222750 (M.op X0 X0) (M.op X1 X0)
       have r₂ := eq36798 X0 X1 x
       grind)
    | (have r₁ := eq222750 (M.op X1 X0) (M.op X0 X0)
       have r₂ := eq36798 X0 X1 x
       grind)
    | exact resolve eq222750 eq36798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36798 eq222750
  have eq222898 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq222819 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222819
  have eq223154 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (k X0 X2) ∨ X0 = X2 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222898 (M.op X2 X0) X1
       have i₂ := eq129610 X0 X2 X0
       grind)
    | exact superpose eq129610 eq222898
    | (have j1 := eq129610 X0 X1 x
       grind)
    | (have r₁ := eq222898 X2 X2
       have r₂ := eq129610 X2 X2 x
       grind)
    | (have r₁ := eq222898 X0 (M.op (M.op X0 X0) X2)
       have r₂ := eq129610 (M.op X0 X0) X2 x
       grind)
    | exact resolve eq222898 eq129610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129610 eq222898
  have eq285130 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79850 X0 (M.op X1 X0) X2
       have i₂ := eq80455 X0 X1
       grind)
    | (have i₁ := eq79850 X1 (M.op X1 X0) X2
       have i₂ := eq80455 X0 X1
       grind)
    | exact superpose eq80455 eq79850
    | (have j0 := eq79850 X0 X1 X2
       have j1 := eq80455 X1 X0
       grind)
    | (have r₁ := eq79850 X0 X1 X0
       have r₂ := eq80455 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq79850 eq80455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79850 eq80455
  have eq286213 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq285130 X0 X1 X2
       have j1 := eq153364 X1 X0
       grind)
    | (have r₁ := eq285130 X0 X1 X1
       have r₂ := eq153364 (M.op X0 (M.op X0 X1)) (M.op X1 X1)
       grind)
    | (have r₁ := eq285130 X2 X0 X2
       have r₂ := eq153364 X0 X2
       grind)
    | (have r₁ := eq285130 X0 (M.op X0 X0) X2
       have r₂ := eq153364 X0 X0
       grind)
    | exact resolve eq285130 eq153364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153364 eq285130
  have eq286405 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq286213 X0 X1 x
       have i₂ := eq8336 X0 X0 X1 x
       grind)
    | exact superpose eq8336 eq286213
    | (have j0 := eq286213 X0 X1 x
       grind)
    | exact resolve eq286213 eq8336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8336 eq286213
  have eq326804 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1324 X1 X1 X1 X2
       have i₂ := eq83479 X1 X0 X1
       grind)
    | exact superpose eq83479 eq1324
    | (have j1 := eq83479 X1 X0 X2
       grind)
    | exact resolve eq1324 eq83479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq326950 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = (M.op X1 (M.op X1 X2)) ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36303 (M.op X1 X2) X1
       have i₂ := eq83479 X1 X0 X2
       grind)
    | exact superpose eq83479 eq36303
    | (have j0 := eq36303 (M.op X1 X2) X1
       have j1 := eq83479 X1 X0 X2
       grind)
    | exact resolve eq36303 eq83479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36303 eq83479
  have eq327701 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq326950 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326950
  have eq327989 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X2 (M.op X1 X2)) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327701 X0 X1 X2
       have i₂ := eq3544 X1 X2 X1
       grind)
    | exact superpose eq3544 eq327701
    | (have j0 := eq327701 X0 X1 X2
       grind)
    | exact resolve eq327701 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327701
  have eq449326 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8439 X1 X0 X1
       have i₂ := eq286405 X1 X0
       grind)
    | exact superpose eq286405 eq8439
    | (have j1 := eq286405 X1 X0
       grind)
    | exact resolve eq8439 eq286405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439 eq286405
  have eq452467 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (M.op X2 (M.op X0 X1)) X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38539 X0 (M.op X0 X1) X2
       have i₂ := eq326804 (M.op X2 (M.op X0 X1)) X0 X1
       grind)
    | exact superpose eq326804 eq38539
    | (have j0 := eq38539 X0 (M.op X0 X1) X2
       have j1 := eq326804 (M.op X2 (M.op X0 X1)) X0 X2
       grind)
    | exact resolve eq38539 eq326804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38539 eq326804
  have eq453476 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X2 (M.op X0 X1)) X0) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452467 X0 X1 X2
       have i₂ := eq3544 X0 X1 X0
       grind)
    | exact superpose eq3544 eq452467
    | (have j0 := eq452467 X0 X1 X2
       grind)
    | (have r₁ := eq452467 X1 X1 X2
       have r₂ := eq3544 X1 X1 X1
       grind)
    | exact resolve eq452467 eq3544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544 eq452467
  have eq454096 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq453476 X0 X1 X2
       have j1 := eq327989 (M.op X2 (M.op X0 X1)) X0 X2
       grind)
    | (have r₁ := eq453476 X1 X2 X2
       have r₂ := eq327989 X0 X1 X2
       grind)
    | (have r₁ := eq453476 X2 X2 X2
       have r₂ := eq327989 X0 X2 X2
       grind)
    | (have r₁ := eq453476 X1 X1 X2
       have r₂ := eq327989 X1 X1 X2
       grind)
    | exact resolve eq453476 eq327989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327989 eq453476
  have eq454256 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) X2)) X2) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = X2 ∨ (M.op X1 X2) ≠ X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq454096 X0 X0 X2
       have i₂ := eq84598 X0 X1 X2
       grind)
    | (have i₁ := eq454096 (M.op X2 X1) X0 X2
       have i₂ := eq84598 X0 X1 X2
       grind)
    | exact superpose eq84598 eq454096
    | (have j1 := eq84598 X2 (M.op X3 (M.op (M.op X0 X1) X2)) X2
       grind)
    | (have r₁ := eq454096 X0 X1 X2
       have r₂ := eq84598 X0 X0 X2
       grind)
    | exact resolve eq454096 eq84598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84598
  have eq454699 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454096 X1 X0 X0
       have i₂ := eq84879 X1 X0
       grind)
    | exact superpose eq84879 eq454096
    | (have j0 := eq454096 X1 X1 x
       have j1 := eq84879 X1 X0
       grind)
    | (have r₁ := eq454096 X0 X1 x
       have r₂ := eq84879 X0 X0
       grind)
    | exact resolve eq454096 eq84879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84879 eq454096
  have eq455003 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq454699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454699
  have eq455083 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = X2 ∨ (M.op X1 X2) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq454256 X0 X1 X2 x
       have i₂ := eq383 (M.op X0 X1) X2 x
       grind)
    | exact superpose eq383 eq454256
    | (have j0 := eq454256 X0 X1 X2 x
       grind)
    | exact resolve eq454256 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq454256
  have eq455101 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = X2 ∨ (M.op X1 X2) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq455083 X0 X1 X2
       have j1 := eq455003 X1 X2
       grind)
    | (have r₁ := eq455083 X0 X1 X1
       have r₂ := eq455003 X0 X1
       grind)
    | (have r₁ := eq455083 X0 X1 X1
       have r₂ := eq455003 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq455083 X0 X1 X1
       have r₂ := eq455003 X0 X1
       grind)
    | exact resolve eq455083 eq455003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455083
  have eq456234 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84874 X0 X1
       have i₂ := eq455101 X1 X1 X0
       grind)
    | exact superpose eq455101 eq84874
    | (have j0 := eq84874 X0 X1
       have j1 := eq455101 X0 X1 X0
       grind)
    | (have r₁ := eq84874 x X1
       have r₂ := eq455101 X1 X1 x
       grind)
    | exact resolve eq84874 eq455101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84874
  have eq456235 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 X1)) = X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84875 X0 X1
       have i₂ := eq455101 X1 X1 X0
       grind)
    | exact superpose eq455101 eq84875
    | (have j0 := eq84875 X0 X1
       have j1 := eq455101 X0 X1 X0
       grind)
    | (have r₁ := eq84875 x X1
       have r₂ := eq455101 X1 X1 x
       grind)
    | exact resolve eq84875 eq455101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84875
  have eq456834 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X3 (M.op X1 X2)) X0) = X0 ∨ (M.op X2 X0) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34169 X2 (M.op X0 X1) X2
       have i₂ := eq455101 X0 X1 X2
       grind)
    | exact superpose eq455101 eq34169
    | (have j1 := eq455101 X3 (M.op X1 X2) X0
       grind)
    | exact resolve eq34169 eq455101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34169 eq455101
  have eq457577 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq456235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456235
  have eq457578 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq456234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456234
  have eq457750 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X2)) X0) = X0 ∨ (M.op X2 X0) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq456834 X0 X1 X2 X3
       have j1 := eq455003 X2 X0
       grind)
    | (have r₁ := eq456834 X1 X1 X2 X3
       have r₂ := eq455003 X0 X1
       grind)
    | (have r₁ := eq456834 X1 X1 X2 X3
       have r₂ := eq455003 (M.op X3 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq456834 X1 X1 X1 X3
       have r₂ := eq455003 X0 X1
       grind)
    | exact resolve eq456834 eq455003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455003 eq456834
  have eq462840 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k X1 X2) ∨ X1 = X2 ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223154 X0 X0 X2
       have i₂ := eq457578 X0 X1
       grind)
    | (have i₁ := eq223154 X0 X1 X2
       have i₂ := eq457578 X0 X1
       grind)
    | exact superpose eq457578 eq223154
    | (have j0 := eq223154 X1 X0 X2
       have j1 := eq457578 X1 X0
       grind)
    | (have r₁ := eq223154 (M.op X1 X0) X1 X0
       have r₂ := eq457578 X0 X1
       grind)
    | (have r₁ := eq223154 X0 X1 (M.op X1 X0)
       have r₂ := eq457578 X0 X1
       grind)
    | (have r₁ := eq223154 (M.op X0 X0) X0 X2
       have r₂ := eq457578 X0 (M.op X0 X0)
       grind)
    | exact resolve eq223154 eq457578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223154
  have eq463275 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ (M.op X0 x))) ∨ x ≠ (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq82840
       have i₂ := eq457578 x X0
       grind)
    | (have i₁ := eq82840
       have i₂ := eq457578 x x
       grind)
    | exact superpose eq457578 eq82840
    | (have j1 := eq457578 x X0
       grind)
    | exact resolve eq82840 eq457578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464270 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k X1 X2) ∨ X1 = X2 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq462840 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462840
  have eq500694 : ∀ X2 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ x ∨ x ≠ (M.op X2 x) := by
    intro X2
    first
    | (have i₁ := eq463275 (M.op x (M.op x X2))
       have i₂ := eq457750 x x X2 x
       grind)
    | exact superpose eq457750 eq463275
    | (have j0 := eq463275 X2
       have j1 := eq457750 (σ x) x (σ x) x
       grind)
    | (have r₁ := eq463275 (M.op x (M.op x X2))
       have r₂ := eq457750 x x X2 x
       grind)
    | exact resolve eq463275 eq457750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463275
  have eq500701 : ∀ X2 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op X2 x) := by
    intro X2
    first
    | (have j0 := eq500694 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500694
  have eq500736 : ∀ X0 X1 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ x ≠ (M.op X1 x) ∨ (σ x) ≠ (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq500701 X1
       have i₂ := eq457578 (σ x) X0
       grind)
    | (have i₁ := eq500701 x
       have i₂ := eq457578 (σ x) (σ x)
       grind)
    | exact superpose eq457578 eq500701
    | (have j0 := eq500701 X1
       have j1 := eq457578 (σ x) X0
       grind)
    | exact resolve eq500701 eq457578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457578 eq500701
  have eq500737 : ∀ X0 X1 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ x ≠ (M.op X1 x) := by
    intro X0 X1
    first
    | (have j0 := eq500736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500736
  have eq522513 : ∀ X0 X3 X4 : G, (k X0 X4) ≠ X0 ∨ X0 = X4 ∨ X0 ≠ X0 ∨ (M.op X3 X0) ≠ X0 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq464270 (M.op X3 (M.op x x)) X0 x
       have i₂ := eq457750 X0 x x X3
       grind)
    | exact superpose eq457750 eq464270
    | (have j0 := eq464270 X3 X0 X4
       have j1 := eq457750 X0 x X3 X3
       grind)
    | (have r₁ := eq464270 X0 (M.op x X0) X0
       have r₂ := eq457750 X0 x x X3
       grind)
    | (have r₁ := eq464270 X0 X0 (M.op x X0)
       have r₂ := eq457750 X0 x x X3
       grind)
    | (have r₁ := eq464270 (M.op X3 (M.op x x)) X0 x
       have r₂ := eq457750 X0 x x X3
       grind)
    | exact resolve eq464270 eq457750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457750
  have eq522818 : ∀ X0 X3 X4 : G, (M.op X3 X0) ≠ X0 ∨ X0 = X4 ∨ (k X0 X4) ≠ X0 := by
    intro X0 X3 X4
    first
    | (have j0 := eq522513 X0 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522513
  have eq675879 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq149918 X0 (M.op X1 X1)
       have i₂ := eq449326 X1 X0
       grind)
    | (have i₁ := eq149918 X1 (M.op X1 X0)
       have i₂ := eq449326 X0 X1
       grind)
    | exact superpose eq449326 eq149918
    | (have j0 := eq149918 X0 (M.op X0 X1)
       have j1 := eq449326 (M.op X0 (M.op X0 X1)) X0
       grind)
    | (have r₁ := eq149918 (M.op X1 X0) X1
       have r₂ := eq449326 X0 X1
       grind)
    | (have r₁ := eq149918 X1 (M.op X1 X0)
       have r₂ := eq449326 X0 X1
       grind)
    | exact resolve eq149918 eq449326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449326
  have eq677650 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq675879 X0 X1
       have j1 := eq149918 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq675879 X1 X1
       have r₂ := eq149918 (M.op X1 (M.op X1 (M.op X1 X1))) X1
       grind)
    | (have r₁ := eq675879 X0 X1
       have r₂ := eq149918 X0 (M.op X0 (M.op X0 (M.op X0 X1)))
       grind)
    | (have r₁ := eq675879 (M.op (M.op X1 X1) (M.op (M.op X1 X1) X1)) X1
       have r₂ := eq149918 (M.op X1 X1) X1
       grind)
    | exact resolve eq675879 eq149918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149918 eq675879
  have eq678885 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq677650 X0 X1
       have i₂ := eq11240 X0 (M.op X0 X1)
       grind)
    | exact superpose eq11240 eq677650
    | (have j0 := eq677650 X0 X1
       have j1 := eq11240 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq677650 X0 X1
       have r₂ := eq11240 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq677650 X1 X1
       have r₂ := eq11240 (M.op X1 (M.op X1 (M.op X1 X1))) X1
       grind)
    | (have r₁ := eq677650 X0 X1
       have r₂ := eq11240 X0 (M.op X0 (M.op X0 (M.op X0 X1)))
       grind)
    | exact resolve eq677650 eq11240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11240 eq677650
  have eq679002 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq678885 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678885
  have eq679041 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq679002 X0 X1
       have j1 := eq87795 X1 X0
       grind)
    | (have r₁ := eq679002 X0 X0
       have r₂ := eq87795 X0 X0
       grind)
    | (have r₁ := eq679002 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq87795 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq679002 X1 X0
       have r₂ := eq87795 X0 X1
       grind)
    | exact resolve eq679002 eq87795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87795 eq679002
  have eq679325 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq679041 X0 X1
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq679041
    | (have j0 := eq679041 (k (M.op X0 X1) X0) X0
       grind)
    | exact resolve eq679041 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679041
  have eq680799 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq679325 X1 (M.op X0 X0)
       have i₂ := eq457577 X1 X0
       grind)
    | exact superpose eq457577 eq679325
    | (have j0 := eq679325 (k X0 X1) X1
       have j1 := eq457577 X1 X0
       grind)
    | (have r₁ := eq679325 X0 X0
       have r₂ := eq457577 X0 X0
       grind)
    | (have r₁ := eq679325 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq457577 (M.op X1 X1) X1
       grind)
    | exact resolve eq679325 eq457577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457577 eq679325
  have eq682671 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq680799 X0 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq680799
    | (have j0 := eq680799 X0 X1
       grind)
    | exact resolve eq680799 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq680799
  have eq691783 : ∀ X0 X1 : G, (k X1 (k X0 X1)) = X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12275 X1
       have i₂ := eq682671 X0 X1
       grind)
    | exact superpose eq682671 eq12275
    | (have j1 := eq682671 X0 X1
       grind)
    | (have r₁ := eq12275 X1
       have r₂ := eq682671 X1 X1
       grind)
    | exact resolve eq12275 eq682671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682671
  have eq693343 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have j0 := eq691783 X0 X1
       have j1 := eq522818 X1 X0 (k X0 X1)
       grind)
    | (have r₁ := eq691783 X0 X0
       have r₂ := eq522818 X0 x (k X0 X0)
       grind)
    | (have r₁ := eq691783 X0 X0
       have r₂ := eq522818 X0 x X0
       grind)
    | (have r₁ := eq691783 (M.op x X0) X0
       have r₂ := eq522818 X0 x x
       grind)
    | exact resolve eq691783 eq522818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522818 eq691783
  have eq693547 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14840 X0 X1
       have i₂ := eq693343 X0 X1
       grind)
    | exact superpose eq693343 eq14840
    | (have j0 := eq14840 (k X0 (M.op X1 X0)) X0
       have j1 := eq693343 (k X0 (M.op X1 X0)) X0
       grind)
    | (have r₁ := eq14840 (M.op X0 X1) X1
       have r₂ := eq693343 X0 X1
       grind)
    | (have r₁ := eq14840 X1 (M.op X0 X1)
       have r₂ := eq693343 X0 X1
       grind)
    | exact resolve eq14840 eq693343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14840 eq693343
  have eq693669 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq693547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693547
  have eq700278 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq693669 X0 (M.op X0 X1)
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq693669
    | (have j0 := eq693669 X0 X0
       grind)
    | exact resolve eq693669 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq693669
  have eq700932 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq700278 X0 X1
       have j1 := eq12275 X0
       grind)
    | (have r₁ := eq700278 X0 X1
       have r₂ := eq12275 X0
       grind)
    | exact resolve eq700278 eq12275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12275 eq700278
  have eq704562 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq217992 X0 X1
       have i₂ := eq700932 X0 (k X0 X1)
       grind)
    | exact superpose eq700932 eq217992
    | (have j0 := eq217992 X0 X1
       have j1 := eq700932 X0 X1
       grind)
    | (have r₁ := eq217992 X0 X1
       have r₂ := eq700932 X0 (k X0 X1)
       grind)
    | exact resolve eq217992 eq700932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217992 eq700932
  have eq704869 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq704562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704562
  have eq707649 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq704869 (k X0 (M.op X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704869
  have eq707650 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq707649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707649
  have eq707888 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X1 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq707650 X1
       have i₂ := eq78225 X1 X0
       grind)
    | exact superpose eq78225 eq707650
    | (have j1 := eq78225 X1 X0
       grind)
    | exact resolve eq707650 eq78225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78225
  have eq708122 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq707650 (σ X0)
       grind)
    | exact superpose eq707650 eq34
    | exact resolve eq34 eq707650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq707650
  have eq708148 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq708122 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq708122
    | exact resolve eq708122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708122
  have eq713529 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq464270 X1 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq708148 X0
       grind)
    | exact superpose eq708148 eq464270
    | (have j0 := eq464270 X0 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq464270 eq708148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464270 eq708148
  have eq713555 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq713529 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713529
  have eq787871 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq707888 (M.op X0 X0) X1
       have i₂ := eq144618 X0 X1
       grind)
    | exact superpose eq144618 eq707888
    | (have j1 := eq144618 X0 X1
       grind)
    | (have r₁ := eq707888 (M.op X0 X0) X0
       have r₂ := eq144618 X0 X0
       grind)
    | exact resolve eq707888 eq144618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144618 eq707888
  have eq788600 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq787871 X0 X1
       have j1 := eq150264 X0 X1
       grind)
    | (have r₁ := eq787871 X0 X1
       have r₂ := eq150264 X0 X1
       grind)
    | (have r₁ := eq787871 X1 X0
       have r₂ := eq150264 X0 X1
       grind)
    | (have r₁ := eq787871 X0 X1
       have r₂ := eq150264 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq787871 eq150264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150264 eq787871
  have eq788887 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq788600 X0 X1
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq788600
    | (have j0 := eq788600 X0 X1
       grind)
    | exact resolve eq788600 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788600
  have eq1107038 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq83206
       have i₂ := eq788887 x x
       grind)
    | exact superpose eq788887 eq83206
    | (have j1 := eq788887 x x
       grind)
    | exact resolve eq83206 eq788887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83206 eq788887
  have eq1107103 : (σ x) = (σ (M.op x x)) := by grind
  clear eq1107038
  have eq1107252 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82840
       have i₂ := eq1107103
       grind)
    | exact superpose eq1107103 eq82840
    | exact resolve eq82840 eq1107103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82840
  have eq1107257 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1107103
       grind)
    | exact superpose eq1107103 eq10
    | exact resolve eq10 eq1107103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107103
  have eq1107336 : x = (M.op x x) := by
    first
    | (have i₁ := eq1107257
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1107257
    | exact resolve eq1107257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107257
  have eq1107423 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq500737 X0 x
       grind)
    | (have r₁ := eq500737 X0 x
       have r₂ := eq1107336
       grind)
    | exact resolve eq500737 eq1107336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500737
  have eq1109051 : x ≠ x ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq713555 x x
       have i₂ := eq1107336
       grind)
    | exact superpose eq1107336 eq713555
    | (have j0 := eq713555 x x
       grind)
    | (have r₁ := eq713555 x x
       have r₂ := eq1107336
       grind)
    | exact resolve eq713555 eq1107336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713555 eq1107336
  have eq1109185 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq1109051
  have eq1109828 : ∀ X0 : G, (τ (M.op (M.op X0 (σ x)) (σ x))) = (k (τ (M.op X0 (σ x))) x) := by
    intro X0
    first
    | (have j0 := eq13578 (M.op X0 (σ x)) x
       grind)
    | (have r₁ := eq13578 (M.op X0 (σ x)) x
       have r₂ := eq1107423 X0
       grind)
    | exact resolve eq13578 eq1107423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13578
  have eq1111215 : ∀ X0 X1 : G, (k (k (M.op X0 (σ x)) (σ x)) (σ X1)) = (k (M.op (M.op X0 (σ x)) (σ x)) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq13662 (M.op X0 (σ x)) (σ x) X1
       grind)
    | (have r₁ := eq13662 (σ x) (M.op X0 (σ x)) x
       have r₂ := eq1107423 X0
       grind)
    | (have r₁ := eq13662 (M.op X0 (σ x)) (σ x) x
       have r₂ := eq1107423 X0
       grind)
    | exact resolve eq13662 eq1107423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13662 eq1107423
  have eq1112199 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (k (τ (M.op X0 (σ x))) x) := by
    intro X0
    first
    | (have i₁ := eq1109828 X0
       have i₂ := eq100 (σ x) X0
       grind)
    | exact superpose eq100 eq1109828
    | exact resolve eq1109828 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109828
  have eq1112989 : ∀ X0 X1 : G, (k (k (M.op X0 (σ x)) (σ x)) (σ X1)) = (k (M.op (σ x) (σ x)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1111215 X0 X1
       have i₂ := eq100 (σ x) X0
       grind)
    | exact superpose eq100 eq1111215
    | exact resolve eq1111215 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1111215
  have eq1113550 : ∀ X0 : G, x = (k (τ (M.op X0 (σ x))) x) := by
    intro X0
    first
    | (have i₁ := eq1112199 X0
       have i₂ := eq1109185
       grind)
    | exact superpose eq1109185 eq1112199
    | exact resolve eq1112199 eq1109185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109185 eq1112199
  have eq1113913 : ∀ X0 X1 : G, (k (M.op (σ x) (σ x)) (σ X1)) = (σ (k (k (τ (M.op X0 (σ x))) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1112989 X0 X1
       have i₂ := eq25 (M.op X0 (σ x)) x X1
       grind)
    | exact superpose eq25 eq1112989
    | exact resolve eq1112989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1112989
  have eq1114425 : ∀ X1 : G, (σ (k x X1)) = (k (M.op (σ x) (σ x)) (σ X1)) := by
    intro X1
    first
    | (have i₁ := eq1113913 x X1
       have i₂ := eq1113550 x
       grind)
    | exact superpose eq1113550 eq1113913
    | exact resolve eq1113913 eq1113550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113550 eq1113913
  have eq1120482 : (σ x) ≠ (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have j0 := eq212774 (σ x) (M.op (σ x) (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq212774 eq1107252
  have eq1121859 : (σ x) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq1120482
       have i₂ := eq1114425 x
       grind)
    | exact superpose eq1114425 eq1120482
    | exact resolve eq1120482 eq1114425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114425 eq1120482
  have eq1122667 : (σ x) ≠ (σ x) := by grind
  clear eq1121859
  have eq1122668 : False := by grind
  exact eq1122668

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq83 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq84 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq84
    | exact resolve eq84 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq9
    | exact resolve eq9 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq160 x y
       grind)
    | exact superpose eq160 eq16
    | (have j1 := eq160 x y
       grind)
    | exact resolve eq16 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq380 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1 (M.op X0 X0)
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq98
    | exact resolve eq98 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq98 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq83 X1 X1 X0 X2
       grind)
    | exact superpose eq83 eq98
    | exact resolve eq98 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq98
  have eq571 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq381 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq84 (M.op X0 X1)
       grind)
    | exact superpose eq84 eq381
    | exact resolve eq381 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq613 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq571 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq571
    | exact resolve eq571 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq571
  have eq4298 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq353
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq353
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq353
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq353
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq353 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq4299 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq4298
  have eq74893 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4299
       grind)
    | exact superpose eq4299 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4299
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4299
       grind)
    | exact resolve eq13 eq4299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4299
  have eq75018 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq74893
  have eq75019 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq75018
  have eq75077 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq75019
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq75019
    | exact resolve eq75019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75019
  have eq891696 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq75077
       grind)
    | exact superpose eq75077 eq10
    | exact resolve eq10 eq75077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75077
  have eq892209 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq891696
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq891696
    | exact resolve eq891696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891696
  have eq892210 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq892209
       have r₂ := eq13 x y
       grind)
    | exact resolve eq892209 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892209
  have eq892213 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq892210
       grind)
    | exact superpose eq892210 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq892210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892210
  have eq892314 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq892213
  have eq892436 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq380 x y
       have i₂ := eq892314
       grind)
    | exact superpose eq892314 eq380
    | exact resolve eq380 eq892314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040662 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq892314
       have i₂ := eq892436
       grind)
    | exact superpose eq892436 eq892314
    | exact resolve eq892314 eq892436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892314 eq892436
  have eq2041150 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2040662
  have eq2041254 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq2041150
       grind)
    | exact superpose eq2041150 eq84
    | exact resolve eq84 eq2041150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041150
  have eq2042582 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2041254
  have eq2042717 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq380 y x
       have i₂ := eq2042582
       grind)
    | exact superpose eq2042582 eq380
    | exact resolve eq380 eq2042582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq2042721 : (M.op y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq613 y x
       have i₂ := eq2042582
       grind)
    | exact superpose eq2042582 eq613
    | exact resolve eq613 eq2042582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq2049589 : y = (M.op y (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq84 y
       have i₂ := eq2042717
       grind)
    | exact superpose eq2042717 eq84
    | exact resolve eq84 eq2042717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq2042717
  have eq2059372 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2049589
       have i₂ := eq2042582
       grind)
    | exact superpose eq2042582 eq2049589
    | exact resolve eq2049589 eq2042582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049589
  have eq2060092 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2059372
  have eq2060501 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2042721
       have i₂ := eq2060092
       grind)
    | exact superpose eq2060092 eq2042721
    | exact resolve eq2042721 eq2060092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042721 eq2060092
  have eq2060993 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2060501
  have eq2061160 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86 x
       have i₂ := eq2060993
       grind)
    | exact superpose eq2060993 eq86
    | exact resolve eq86 eq2060993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2060993
  have eq2085001 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2061160
       grind)
    | exact superpose eq2061160 eq16
    | exact resolve eq16 eq2061160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061160
  have eq2086016 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2085001
       have i₂ := eq2042582
       grind)
    | exact superpose eq2042582 eq2085001
    | exact resolve eq2085001 eq2042582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042582 eq2085001
  have eq2086017 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2086016
  have eq2086018 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2086017
  have eq2086020 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2086018
       grind)
    | exact superpose eq2086018 eq10
    | exact resolve eq10 eq2086018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086018
  have eq2086613 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2086020
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2086020
    | exact resolve eq2086020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086020
  have eq2086614 : x = y := by grind
  clear eq2086613
  have eq2086619 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2086614
       grind)
    | exact superpose eq2086614 eq16
    | exact resolve eq16 eq2086614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086614
  have eq2086620 : False := by grind
  exact eq2086620

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyx_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X0)) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq351 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq350 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq349 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq350
  have eq415 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq351 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq351
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq456 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq61
    | (have j1 := eq415 X0 (M.op (M.op X1 X0) X0)
       grind)
    | exact resolve eq61 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq457 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq9
    | (have j1 := eq415 X0 (M.op X1 X0)
       grind)
    | exact resolve eq9 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq752 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq457 X0 X1
       grind)
    | exact superpose eq457 eq456
    | (have j0 := eq456 X0 X1
       have j1 := eq457 X0 X1
       grind)
    | exact resolve eq456 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq457
  have eq770 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq752 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq775 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq770 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq770 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq770 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq799 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq775 (σ X1) (σ X0)
       grind)
    | exact superpose eq775 eq15
    | exact resolve eq15 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 X1
       have i₂ := eq775 X1 X0
       grind)
    | exact superpose eq775 eq799
    | exact resolve eq799 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq799
  have eq1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq826 x y
       grind)
    | exact superpose eq826 eq16
    | (have r₁ := eq16
       have r₂ := eq826 x y
       grind)
    | exact resolve eq16 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq1184 : False := by grind
  exact eq1184

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq204 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       have j1 := eq203 X0 X1
       grind)
    | (have r₁ := eq208 X0 X1
       have r₂ := eq203 X0 X1
       grind)
    | (have r₁ := eq208 (k X0 X1) X0
       have r₂ := eq203 X0 X1
       grind)
    | (have r₁ := eq208 X0 X0
       have r₂ := eq203 X0 X0
       grind)
    | exact resolve eq208 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq208
  have eq731 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq213 x y
       grind)
    | exact superpose eq213 eq16
    | (have j1 := eq213 x y
       grind)
    | exact resolve eq16 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq759 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq731
    | (have j0 := eq731 X0 X1
       grind)
    | exact resolve eq731 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq731
  have eq765 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq759 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq759
    | exact resolve eq759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq846 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq765 (τ X0) X1
       grind)
    | exact superpose eq765 eq18
    | (have j1 := eq765 (τ X0) X1
       grind)
    | exact resolve eq18 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq765
  have eq1052 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq846 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq846
    | exact resolve eq846 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1052
    | (have j0 := eq1052 X0 X1
       grind)
    | exact resolve eq1052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq739
       have i₂ := eq1106 x y
       grind)
    | exact superpose eq1106 eq739
    | (have j1 := eq1106 (σ x) (σ y)
       grind)
    | (have r₁ := eq739
       have r₂ := eq1106 x y
       grind)
    | exact resolve eq739 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1217
  have eq1226 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1218
  have eq1239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq739
       have i₂ := eq1226
       grind)
    | exact superpose eq1226 eq739
    | exact resolve eq739 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1226
  have eq1240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1239
  have eq1241 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1240
  have eq1293 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1241
  have eq1309 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1293
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1293
    | exact resolve eq1293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1490 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1309
       grind)
    | exact superpose eq1309 eq16
    | exact resolve eq16 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1490
       have i₂ := eq1106 x y
       grind)
    | exact superpose eq1106 eq1490
    | (have j1 := eq1106 x y
       grind)
    | (have r₁ := eq1490
       have r₂ := eq1106 x y
       grind)
    | exact resolve eq1490 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1554 : x = (M.op y y) := by grind
  clear eq1553
  have eq1560 : (M.op x y) = (k x y) := by grind
  clear eq1554
  have eq1639 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1490
       have i₂ := eq1560
       grind)
    | exact superpose eq1560 eq1490
    | exact resolve eq1490 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490 eq1560
  have eq1642 : False := by grind
  exact eq1642

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation1996 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq49 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq130 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 (τ X0) X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq130
    | exact resolve eq130 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq307 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105 x y
       grind)
    | exact superpose eq105 eq16
    | (have j1 := eq105 x y
       grind)
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq451 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (M.op X0 X0)))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq238 (M.op x (τ (τ (M.op X0 X0)))) X1 X3
       have i₂ := eq238 X0 x (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq238 eq238
    | exact resolve eq238 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (M.op X0 X0))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq130 (M.op x (τ (τ (M.op X0 X0)))) X1 X3
       have i₂ := eq238 X0 x (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq238 eq130
    | exact resolve eq130 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq863 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq481 (M.op x (τ (τ (τ (M.op X0 X0))))) X1 X3
       have i₂ := eq481 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq481 eq481
    | exact resolve eq481 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (τ (τ (τ (M.op X0 X0))))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (M.op x (τ (τ (τ (M.op X0 X0)))))
       have i₂ := eq481 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq481 eq49
    | exact resolve eq49 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq909 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (M.op X0 X0))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq238 (M.op x (τ (τ (τ (M.op X0 X0))))) X1 X3
       have i₂ := eq481 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq481 eq238
    | exact resolve eq238 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq481
  have eq3553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq307
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq307
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq307
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq307
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq3554 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3553
  have eq6786 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq451 (M.op x (τ (τ (τ (τ (τ (M.op X0 X0))))))) X1 X3
       have i₂ := eq909 X0 x (τ (τ (τ (τ (τ (M.op X0 X0))))))
       grind)
    | exact superpose eq909 eq451
    | exact resolve eq451 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq909
  have eq22411 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq899 (M.op x (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))) X1
       have i₂ := eq863 X0 x (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))
       grind)
    | exact superpose eq863 eq899
    | exact resolve eq899 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq899
  have eq68969 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3554
       grind)
    | exact superpose eq3554 eq16
    | exact resolve eq16 eq3554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq68970 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq68969
       have r₂ := eq22 x
       grind)
    | exact resolve eq68969 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68969
  have eq449824 : ∀ X0 : G, y = (M.op (M.op x (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq6786 X0 x y
       have i₂ := eq68970
       grind)
    | exact superpose eq68970 eq6786
    | exact resolve eq6786 eq68970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68970
  have eq449826 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq449824 x
       have i₂ := eq6786 x x x
       grind)
    | (have i₁ := eq449824 x
       have i₂ := eq6786 x x (M.op (M.op x (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op x x))))))))))) (M.op x x))
       grind)
    | exact superpose eq6786 eq449824
    | exact resolve eq449824 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449824
  have eq450841 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq449826
       grind)
    | exact superpose eq449826 eq16
    | exact resolve eq16 eq449826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449826
  have eq450842 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq450841
       have r₂ := eq22 x
       grind)
    | exact resolve eq450841 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450841
  have eq450874 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (σ (M.op x x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6786 X0 (σ x) (σ y)
       have i₂ := eq450842
       grind)
    | exact superpose eq450842 eq6786
    | exact resolve eq6786 eq450842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6786 eq450842
  have eq450884 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq450874 x
       have i₂ := eq22411 x x
       grind)
    | exact superpose eq22411 eq450874
    | exact resolve eq450874 eq22411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22411 eq450874
  have eq450885 : (σ x) = (σ y) := by grind
  clear eq450884
  have eq452075 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq450885
       grind)
    | exact superpose eq450885 eq16
    | exact resolve eq16 eq450885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452076 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq450885
       grind)
    | exact superpose eq450885 eq10
    | exact resolve eq10 eq450885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450885
  have eq452209 : x = y := by
    first
    | (have i₁ := eq452076
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq452076
    | exact resolve eq452076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452076
  have eq452210 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq452075
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq452075
    | exact resolve eq452075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq452075
  have eq452211 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq452210
       have i₂ := eq452209
       grind)
    | exact superpose eq452209 eq452210
    | exact resolve eq452210 eq452209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452209 eq452210
  have eq452212 : False := by grind
  exact eq452212

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq58
    | exact resolve eq58 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq58
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq203
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq203
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | (have r₁ := eq203
       have r₂ := eq81 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq203
       have r₂ := eq81 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq203 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq203
  have eq358 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq355
  have eq359 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq358
       grind)
    | exact superpose eq358 eq16
    | exact resolve eq16 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq360 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq359
       have r₂ := eq67 x
       grind)
    | exact resolve eq359 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq396 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq10
    | exact resolve eq10 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq413 : x = y := by
    first
    | (have i₁ := eq396
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq396
    | exact resolve eq396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq457 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq413
       grind)
    | exact superpose eq413 eq16
    | exact resolve eq16 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq458 : False := by grind
  exact eq458

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq76 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq947 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq946
  have eq950 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq947 eq120
    | exact resolve eq120 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq954 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq950
  have eq959 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq954
       have r₂ := eq131
       grind)
    | exact resolve eq954 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq954
  have eq975 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq959 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq959
       grind)
    | exact resolve eq13 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq977 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq975
  have eq990 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq977
    | exact resolve eq977 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq990 eq120
    | exact resolve eq120 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq990
  have eq1145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1142
  have eq1149 : y = (M.op x y) := by
    first
    | (have r₁ := eq1145
       have r₂ := eq27
       grind)
    | exact resolve eq1145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1151 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1149 eq20
    | exact resolve eq20 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq1149 eq76
    | (have r₁ := eq76
       have r₂ := eq1149
       grind)
    | exact resolve eq76 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1160 : y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq1156
  have eq1166 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1151
    | exact resolve eq1151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1196 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq98
    | (have j0 := eq98 X0 (M.op x y)
       grind)
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq98
  have eq1226 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1149 eq1196
    | (have j0 := eq1196 X0
       grind)
    | exact resolve eq1196 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1241 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1166 eq26
    | exact resolve eq26 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1387 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1226 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1226
    | (have j0 := eq1226 x
       grind)
    | exact resolve eq1226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1226
  have eq1402 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1241 eq1387
    | exact resolve eq1387 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1416 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1402
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1402
    | exact resolve eq1402 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1402
  have eq1425 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1166 eq1416
    | exact resolve eq1416 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1241 eq1425
    | exact resolve eq1425 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241 eq1425
  have eq1431 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1430
       have r₂ := eq27
       grind)
    | exact resolve eq1430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1433 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1431 eq62
    | exact resolve eq62 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1431
  have eq1435 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1149 eq1433
    | exact resolve eq1433 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq1449 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1160
       have i₂ := eq1435
       grind)
    | exact superpose eq1435 eq1160
    | exact resolve eq1160 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1517 : y ≠ y ∨ (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1449
       grind)
    | exact resolve eq13 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1523 : (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1517
  have eq1524 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1523
       have i₂ := eq1435
       grind)
    | exact superpose eq1435 eq1523
    | exact resolve eq1523 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq1523
  have eq1526 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1524
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1524
    | exact resolve eq1524 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1524
  have eq1528 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1149 eq1526
    | exact resolve eq1526 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq1526
  have eq1529 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1528
  have eq1533 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1529 eq15
    | exact resolve eq15 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1534 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1533
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1533
    | exact resolve eq1533 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1533
  have eq1535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1166 eq1534
    | exact resolve eq1534 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq1534
  have eq1536 : False := by grind
  exact eq1536

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq58
    | exact resolve eq58 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq58
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq203
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq203
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | (have r₁ := eq203
       have r₂ := eq81 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq203
       have r₂ := eq81 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq203 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq203
  have eq359 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq356
  have eq360 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq359
       grind)
    | exact superpose eq359 eq16
    | exact resolve eq16 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq361 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq360
       have r₂ := eq67 x
       grind)
    | exact resolve eq360 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq397 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq361
       grind)
    | exact superpose eq361 eq10
    | exact resolve eq10 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq414 : x = y := by
    first
    | (have i₁ := eq397
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq397
    | exact resolve eq397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq458 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq414
       grind)
    | exact superpose eq414 eq16
    | exact resolve eq16 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq459 : False := by grind
  exact eq459
