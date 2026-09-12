import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq79 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3365 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3421 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3365 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq3365
    | (have j0 := eq3365 X0 X1
       grind)
    | exact resolve eq3365 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3690 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq79 (σ X1) X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3699 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3701 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3690 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690
  have eq6924 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3699 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3699
    | (have r₁ := eq3699 X0 (τ X0)
       have r₂ := eq11 X0
       grind)
    | (have r₁ := eq3699 (σ (τ (σ X1))) X1
       have r₂ := eq11 (σ X1)
       grind)
    | exact resolve eq3699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq6946 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6924 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq6924
    | (have j0 := eq6924 X0 X1
       grind)
    | (have r₁ := eq6924 (k (τ X1) (τ X0)) (τ (k X1 X0))
       have r₂ := eq33 X0 X1
       grind)
    | (have r₁ := eq6924 (τ (k X1 X0)) (k (τ X1) (τ X0))
       have r₂ := eq33 X0 X1
       grind)
    | exact resolve eq6924 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6924
  have eq6947 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6946 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6946
  have eq7067 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq6947 X0
       grind)
    | exact superpose eq6947 eq12
    | (have j1 := eq6947 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq6947 X0
       grind)
    | exact resolve eq12 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947
  have eq7090 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7067 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067
  have eq7111 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (τ (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7090 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7090
    | exact resolve eq7090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7090
  have eq7253 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7111 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq7111
    | (have j0 := eq7111 X0
       grind)
    | exact resolve eq7111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7111
  have eq7689 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq7253 X0
       grind)
    | exact superpose eq7253 eq10
    | (have j1 := eq7253 X0
       grind)
    | exact resolve eq10 eq7253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7253
  have eq7753 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7689 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7689
    | (have j0 := eq7689 X0
       grind)
    | exact resolve eq7689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7689
  have eq7920 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq7753 X0
       grind)
    | exact superpose eq7753 eq11
    | (have j1 := eq7753 X0
       grind)
    | exact resolve eq11 eq7753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7753
  have eq8113 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7920 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7920
    | (have j0 := eq7920 (τ X0)
       grind)
    | exact resolve eq7920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7920
  have eq8216 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8113 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq8113
    | (have j0 := eq8113 X0
       grind)
    | exact resolve eq8113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8113
  have eq8221 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8216 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8216
    | (have j0 := eq8216 X0
       grind)
    | exact resolve eq8216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8216
  have eq8222 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8221 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq8221
    | (have j0 := eq8221 X0
       grind)
    | exact resolve eq8221 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8221
  have eq8235 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3421 X0 X0
       have i₂ := eq8222 X0
       grind)
    | exact superpose eq8222 eq3421
    | (have j0 := eq3421 X0 X0
       have j1 := eq8222 X0
       grind)
    | exact resolve eq3421 eq8222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421 eq8222
  have eq8303 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8235
  have eq8364 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8303 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq8303 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq8303 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8303
  have eq8500 : ∀ X0 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq8364 X0
       grind)
    | exact superpose eq8364 eq11
    | (have j1 := eq8364 X0
       grind)
    | exact resolve eq11 eq8364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8364
  have eq8616 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq8500 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8500
    | (have j0 := eq8500 X0
       grind)
    | exact resolve eq8500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500
  have eq8623 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8616 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq8616 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq8616 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8616
  have eq8686 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8623 (σ X0)
       grind)
    | exact superpose eq8623 eq15
    | exact resolve eq15 eq8623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8755 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8686 X0
       have i₂ := eq8623 X0
       grind)
    | exact superpose eq8623 eq8686
    | exact resolve eq8686 eq8623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8623 eq8686
  have eq81323 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3701 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3701
    | exact resolve eq3701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81408 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq3701 X0 X1
       grind)
    | exact superpose eq3701 eq23
    | (have j1 := eq3701 X0 X1
       grind)
    | exact resolve eq23 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3701
  have eq81673 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq81408 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81408
    | (have j0 := eq81408 X0 X1
       grind)
    | exact resolve eq81408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81408
  have eq81698 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81323 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq81323
    | (have j0 := eq81323 X0 X1
       grind)
    | exact resolve eq81323 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81323
  have eq125001 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq81698 X1 X0
       grind)
    | exact superpose eq81698 eq11
    | (have j1 := eq81698 X1 X0
       grind)
    | exact resolve eq11 eq81698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81698
  have eq125228 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125001 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq125001
    | (have j0 := eq125001 X0 X1
       grind)
    | exact resolve eq125001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125001
  have eq125711 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq125228 X0 (τ X1)
       grind)
    | exact superpose eq125228 eq18
    | (have j1 := eq125228 X0 (τ X1)
       grind)
    | exact resolve eq18 eq125228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq125228
  have eq533288 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 (σ (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq81673 (τ X0) X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq81673
    | (have j0 := eq81673 (τ X1) X0
       grind)
    | exact resolve eq81673 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq81673
  have eq534813 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq533288 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq533288
    | (have j0 := eq533288 X0 X1
       grind)
    | exact resolve eq533288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533288
  have eq535452 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq534813 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq534813
    | (have j0 := eq534813 X0 X1
       grind)
    | exact resolve eq534813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534813
  have eq540707 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq535452 X0 X1
       grind)
    | exact superpose eq535452 eq11
    | (have j1 := eq535452 X0 X1
       grind)
    | exact resolve eq11 eq535452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541117 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq535452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535452
  have eq541326 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq540707 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq540707
    | (have j0 := eq540707 X0 X1
       grind)
    | exact resolve eq540707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540707
  have eq545087 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq541326 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq541326
    | (have j0 := eq541326 (σ X0) (σ X1)
       grind)
    | exact resolve eq541326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541326
  have eq546375 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq545087 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq545087
    | (have j0 := eq545087 X0 X1
       grind)
    | exact resolve eq545087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545087
  have eq546523 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq546375 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq546375
    | (have j0 := eq546375 X0 X1
       grind)
    | exact resolve eq546375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546375
  have eq1170711 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq125711 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125711
    | exact resolve eq125711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125711
  have eq1172560 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1170711 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1170711
    | (have j0 := eq1170711 X0 X1
       grind)
    | exact resolve eq1170711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170711
  have eq1247455 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq546523 x y
       grind)
    | exact superpose eq546523 eq16
    | (have j1 := eq546523 x y
       grind)
    | exact resolve eq16 eq546523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248713 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq546523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546523
  have eq1272343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1247455
       have i₂ := eq1172560 y x
       grind)
    | exact superpose eq1172560 eq1247455
    | (have j1 := eq1172560 y x
       grind)
    | (have r₁ := eq1247455
       have r₂ := eq1172560 y x
       grind)
    | exact resolve eq1247455 eq1172560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172560 eq1247455
  have eq1272346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1272343
  have eq1272347 : x = (M.op x y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1272346
  have eq1272354 : x ≠ x ∨ x = (k x y) ∨ x = y ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1272347
       grind)
    | exact superpose eq1272347 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1272347
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1272347
       grind)
    | exact resolve eq13 eq1272347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1272355 : x ≠ y ∨ x = (k x y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1272347
       grind)
    | exact superpose eq1272347 eq12
    | exact resolve eq12 eq1272347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272347
  have eq1272356 : x = (k x y) ∨ x = y ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1272354
  have eq1272359 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1272356
       have r₂ := eq1272355
       grind)
    | exact resolve eq1272356 eq1272355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272355 eq1272356
  have eq1282619 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1272359
       grind)
    | exact superpose eq1272359 eq16
    | exact resolve eq16 eq1272359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282620 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1272359
       grind)
    | exact superpose eq1272359 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1272359
       grind)
    | exact resolve eq13 eq1272359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282621 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq1272359
       grind)
    | exact superpose eq1272359 eq12
    | exact resolve eq12 eq1272359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272359
  have eq1282622 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = (k x y) := by grind
  clear eq1282620
  have eq1282624 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1282621
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1282621
    | exact resolve eq1282621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282621
  have eq1282625 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1282622
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1282622
    | exact resolve eq1282622 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282622
  have eq1282628 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1282625
       have r₂ := eq1282624
       grind)
    | exact resolve eq1282625 eq1282624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282624 eq1282625
  have eq1287545 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1282628
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1282628
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1282628 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282628
  have eq1287598 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1287545
  have eq1293779 : y ≠ y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1287598
       grind)
    | exact superpose eq1287598 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq1287598
       grind)
    | exact resolve eq12 eq1287598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287598
  have eq1293781 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x y) := by grind
  clear eq1293779
  have eq1301971 : (σ x) ≠ (σ x) ∨ y = (k x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1282619
       have i₂ := eq1293781
       grind)
    | exact superpose eq1293781 eq1282619
    | (have r₁ := eq1282619
       have r₂ := eq1293781
       grind)
    | exact resolve eq1282619 eq1293781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293781
  have eq1301975 : (σ x) ≠ (σ x) ∨ y = (k x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1301971
  have eq1301976 : y = (k x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1301975
  have eq1301979 : y = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1301976
       have r₂ := eq1282619
       grind)
    | exact resolve eq1301976 eq1282619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282619 eq1301976
  have eq1301982 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1301979
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1301979
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1301979 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302029 : x ≠ y ∨ x = (k x y) := by grind
  clear eq1301979
  have eq1302035 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1301982
  have eq1306878 : (τ y) ≠ (τ y) ∨ x = y ∨ (τ y) = (τ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq541117 x y
       have i₂ := eq1302035
       grind)
    | exact superpose eq1302035 eq541117
    | (have j0 := eq541117 x y
       grind)
    | exact resolve eq541117 eq1302035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541117
  have eq1306881 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq1306884 : x = y ∨ (τ y) = (τ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq1306878
  have eq1306886 : x = (M.op x y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq1306884
       have r₂ := eq1306881
       grind)
    | exact resolve eq1306884 eq1306881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306881 eq1306884
  have eq1316582 : x ≠ x ∨ x = (k x y) ∨ x = y ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1306886
       grind)
    | exact superpose eq1306886 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1306886
       grind)
    | exact resolve eq13 eq1306886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316584 : x = (k x y) ∨ x = y ∨ (τ y) = (τ (k x y)) := by grind
  clear eq1316582
  have eq1316586 : x = (k x y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq1316584
       have r₂ := eq1302029
       grind)
    | exact resolve eq1316584 eq1302029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316584
  have eq1316647 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq1248713 x y
       have i₂ := eq1316586
       grind)
    | exact superpose eq1316586 eq1248713
    | (have j0 := eq1248713 x y
       grind)
    | exact resolve eq1248713 eq1316586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248713 eq1316586
  have eq1316650 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (τ y) = (τ (k x y)) := by grind
  clear eq1316647
  have eq1347618 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1316650
       grind)
    | exact superpose eq1316650 eq16
    | exact resolve eq16 eq1316650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316650
  have eq1347636 : (σ x) ≠ (σ x) ∨ x = y ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq1347618
       have i₂ := eq1306886
       grind)
    | exact superpose eq1306886 eq1347618
    | exact resolve eq1347618 eq1306886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306886 eq1347618
  have eq1347639 : (σ x) ≠ (σ x) ∨ x = y ∨ (τ y) = (τ (k x y)) := by grind
  clear eq1347636
  have eq1347640 : x = y ∨ (τ y) = (τ (k x y)) := by grind
  clear eq1347639
  have eq1351555 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1347640
       grind)
    | exact superpose eq1347640 eq16
    | exact resolve eq16 eq1347640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347640
  have eq1351640 : (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq1351555
       have r₂ := eq8755 x
       grind)
    | exact resolve eq1351555 eq8755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351555
  have eq1351669 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq1351640
       grind)
    | exact superpose eq1351640 eq11
    | exact resolve eq11 eq1351640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351640
  have eq1353136 : y = (k x y) := by
    first
    | (have i₁ := eq1351669
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq1351669
    | exact resolve eq1351669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351669
  have eq1357566 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq268 x y
       have i₂ := eq1353136
       grind)
    | exact superpose eq1353136 eq268
    | (have j0 := eq268 x y
       grind)
    | exact resolve eq268 eq1353136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq1357612 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1357566
  have eq1395729 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1357612
       grind)
    | exact superpose eq1357612 eq16
    | exact resolve eq16 eq1357612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1395735 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1357612
  have eq1401570 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1395729
       have i₂ := eq1302035
       grind)
    | exact superpose eq1302035 eq1395729
    | exact resolve eq1395729 eq1302035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302035 eq1395729
  have eq1401574 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1401570
  have eq1401593 : x ≠ x ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1401574
       grind)
    | exact superpose eq1401574 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1401574
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1401574
       grind)
    | exact resolve eq13 eq1401574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401574
  have eq1401595 : x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1401593
  have eq1401602 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1401595
       have r₂ := eq1302029
       grind)
    | exact resolve eq1401595 eq1302029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302029 eq1401595
  have eq1401603 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1401602
       have i₂ := eq1353136
       grind)
    | exact superpose eq1353136 eq1401602
    | exact resolve eq1401602 eq1353136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401602
  have eq1409061 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1401603
       grind)
    | exact superpose eq1401603 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1401603
       grind)
    | exact resolve eq13 eq1401603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401603
  have eq1409063 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1409061
  have eq1409065 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1409063
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1409063
    | exact resolve eq1409063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409063
  have eq1409069 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1409065
       have i₂ := eq1353136
       grind)
    | exact superpose eq1353136 eq1409065
    | exact resolve eq1409065 eq1353136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353136 eq1409065
  have eq1409070 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1409069
  have eq1409071 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1409070
       grind)
    | exact superpose eq1409070 eq16
    | exact resolve eq16 eq1409070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409070
  have eq1409184 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1409071
       have r₂ := eq8755 x
       grind)
    | exact resolve eq1409071 eq8755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409071
  have eq1414393 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1409184
       grind)
    | exact superpose eq1409184 eq16
    | exact resolve eq16 eq1409184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1414397 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1395735
       have i₂ := eq1409184
       grind)
    | exact superpose eq1409184 eq1395735
    | (have r₁ := eq1395735
       have r₂ := eq1409184
       grind)
    | exact resolve eq1395735 eq1409184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395735
  have eq1414399 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1409184
       grind)
    | exact superpose eq1409184 eq10
    | exact resolve eq10 eq1409184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409184
  have eq1414832 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1414397
  have eq1414988 : x = y := by
    first
    | (have i₁ := eq1414399
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1414399
    | exact resolve eq1414399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414399
  have eq1414990 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1414832
       have i₂ := eq8755 x
       grind)
    | exact superpose eq8755 eq1414832
    | exact resolve eq1414832 eq8755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414832
  have eq1414992 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1414393
       have i₂ := eq8755 x
       grind)
    | exact superpose eq8755 eq1414393
    | exact resolve eq1414393 eq8755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8755 eq1414393
  have eq1415063 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1414992
       have i₂ := eq1414990
       grind)
    | exact superpose eq1414990 eq1414992
    | exact resolve eq1414992 eq1414990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414992
  have eq1415114 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1415063
       have i₂ := eq1414988
       grind)
    | exact superpose eq1414988 eq1415063
    | exact resolve eq1415063 eq1414988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414988 eq1415063
  have eq1415149 : False := by grind
  exact eq1415149

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq104 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (k X1 (σ X2))
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq14
    | (have j0 := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq14 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq12
    | (have j1 := eq73 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq73 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq742 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq743 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq742 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq742
    | (have j0 := eq742 X0
       grind)
    | exact resolve eq742 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq742
  have eq747 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq743 X0
       have j1 := eq741 X0
       grind)
    | (have r₁ := eq743 X0
       have r₂ := eq741 X0
       grind)
    | exact resolve eq743 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq743
  have eq757 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq747 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq747
    | exact resolve eq747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (k X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq9
    | exact resolve eq9 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq757 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq757
    | exact resolve eq757 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq757
  have eq785 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq782 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq782
    | exact resolve eq782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq803 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq785 (σ X0)
       grind)
    | exact superpose eq785 eq15
    | exact resolve eq15 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq803 X0
       have i₂ := eq785 X0
       grind)
    | exact superpose eq785 eq803
    | exact resolve eq803 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq943 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ (k X1 X1)) (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X1 (τ X0)
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq768
    | exact resolve eq768 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq950 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ (k X1 X1)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq943 X0 X1
       have i₂ := eq785 X0
       grind)
    | exact superpose eq785 eq943
    | exact resolve eq943 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq962 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X1 X1)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X1
       have i₂ := eq785 X1
       grind)
    | exact superpose eq785 eq950
    | exact resolve eq950 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq40011 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X0) (k X1 (σ X2))
       have i₂ := eq104 X0 X1 X2
       grind)
    | exact superpose eq104 eq12
    | (have j0 := eq12 (σ X0) (k X1 (σ X2))
       have j1 := eq104 X0 X1 X2
       grind)
    | (have r₁ := eq12 (σ X0) (k X1 (σ X2))
       have r₂ := eq104 X0 X1 X2
       grind)
    | exact resolve eq12 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq40012 : ∀ X0 X1 X2 : G, (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40011 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40011
  have eq40016 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40012 X0 X1 X2
       have i₂ := eq22 X1 X2 X0
       grind)
    | exact superpose eq22 eq40012
    | (have j0 := eq40012 X0 X1 X2
       grind)
    | exact resolve eq40012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40012
  have eq40017 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40016 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40016
  have eq40362 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k (τ X1) X2)
       have i₂ := eq40017 (τ X0) X1 X2
       grind)
    | exact superpose eq40017 eq18
    | (have j1 := eq40017 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq40017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40017
  have eq40488 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40362 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40362
    | (have j0 := eq40362 X0 X1 X2
       grind)
    | exact resolve eq40362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40362
  have eq40567 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40488 X0 X1 X2
       have i₂ := eq18 X1 X2
       grind)
    | exact superpose eq18 eq40488
    | (have j0 := eq40488 X0 X1 X2
       grind)
    | exact resolve eq40488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40488
  have eq40638 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40567 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40567
    | (have j0 := eq40567 X0 X1 X2
       grind)
    | exact resolve eq40567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40567
  have eq40831 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op X1 (k X2 X0)) ∨ (k X2 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40638 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40638
    | exact resolve eq40638 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40638
  have eq41476 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40831 X0 X1 X0
       have i₂ := eq785 X0
       grind)
    | exact superpose eq785 eq40831
    | (have j0 := eq40831 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact resolve eq40831 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41750 : ∀ X0 X1 : G, (σ (M.op (τ X0) (M.op X1 X1))) = (k X0 (σ (M.op X1 X1))) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq41476 X1 (τ X0)
       grind)
    | exact superpose eq41476 eq18
    | (have j1 := eq41476 X1 (τ X0)
       grind)
    | exact resolve eq18 eq41476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq49237 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq41750 X0 (τ (M.op X0 X0))
       have i₂ := eq962 X0 X0
       grind)
    | exact superpose eq962 eq41750
    | (have j0 := eq41750 X0 (τ (M.op X0 X0))
       grind)
    | exact resolve eq41750 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962 eq41750
  have eq49357 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (k (M.op X0 X0) (M.op X0 X0))))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49237 X0
       have i₂ := eq747 (M.op X0 X0)
       grind)
    | exact superpose eq747 eq49237
    | (have j0 := eq49237 X0
       grind)
    | exact resolve eq49237 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49237
  have eq49380 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49357 X0
       have i₂ := eq11 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq49357
    | (have j0 := eq49357 X0
       grind)
    | exact resolve eq49357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49357
  have eq49388 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49380 X0
       have i₂ := eq785 (M.op X0 X0)
       grind)
    | exact superpose eq785 eq49380
    | (have j0 := eq49380 X0
       grind)
    | exact resolve eq49380 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49380
  have eq49394 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49388 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49388
    | (have j0 := eq49388 X0
       grind)
    | exact resolve eq49388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49388
  have eq49399 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq49394 X0
       have i₂ := eq747 (M.op X0 X0)
       grind)
    | exact superpose eq747 eq49394
    | (have j0 := eq49394 X0
       grind)
    | exact resolve eq49394 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq49394
  have eq49403 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49399 X0
       have i₂ := eq785 (M.op X0 X0)
       grind)
    | exact superpose eq785 eq49399
    | (have j0 := eq49399 X0
       grind)
    | exact resolve eq49399 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq49399
  have eq120115 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))))) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30 X0 (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))
       have i₂ := eq49403 (σ X0)
       grind)
    | exact superpose eq49403 eq30
    | (have j1 := eq49403 (σ X0)
       grind)
    | exact resolve eq30 eq49403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq49403
  have eq120282 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120115 X0
       have i₂ := eq821 X0
       grind)
    | exact superpose eq821 eq120115
    | (have j0 := eq120115 X0
       grind)
    | exact resolve eq120115 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120115
  have eq120362 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (M.op X0 X0) (M.op X0 X0))))) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120282 X0
       have i₂ := eq821 (M.op X0 X0)
       grind)
    | exact superpose eq821 eq120282
    | (have j0 := eq120282 X0
       grind)
    | exact resolve eq120282 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120282
  have eq120429 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120362 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq120362
    | (have j0 := eq120362 X0
       grind)
    | exact resolve eq120362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120362
  have eq120494 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (τ (σ X0)) = (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq120429 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120429
    | (have j0 := eq120429 X0
       grind)
    | exact resolve eq120429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120429
  have eq120551 : ∀ X0 : G, (τ (σ X0)) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq120494 X0
       have i₂ := eq821 X0
       grind)
    | exact superpose eq821 eq120494
    | (have j0 := eq120494 X0
       grind)
    | exact resolve eq120494 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120494
  have eq120607 : ∀ X0 : G, (τ (σ X0)) = (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq120551 X0
       have i₂ := eq821 (M.op X0 X0)
       grind)
    | exact superpose eq821 eq120551
    | (have j0 := eq120551 X0
       grind)
    | exact resolve eq120551 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120551
  have eq120661 : ∀ X0 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq120607 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq120607
    | (have j0 := eq120607 X0
       grind)
    | exact resolve eq120607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120607
  have eq120708 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq120661 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120661
    | (have j0 := eq120661 X0
       grind)
    | exact resolve eq120661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120661
  have eq121022 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40831 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X0
       have i₂ := eq120708 X0
       grind)
    | exact superpose eq120708 eq40831
    | (have j0 := eq40831 X0 (M.op X1 X0) X1
       have j1 := eq120708 X0
       grind)
    | exact resolve eq40831 eq120708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40831 eq120708
  have eq122055 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41476 (M.op X0 X0) X1
       have i₂ := eq121022 X0 X1
       grind)
    | exact superpose eq121022 eq41476
    | (have j1 := eq121022 X0 X1
       grind)
    | exact resolve eq41476 eq121022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41476 eq121022
  have eq151292 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122055 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122055
  have eq151293 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq151292 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151292
  have eq151294 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq151293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151293
  have eq152701 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq151294 X0 (τ X1)
       grind)
    | exact superpose eq151294 eq19
    | (have j1 := eq151294 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq151294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq152810 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq151294 (σ X0) (σ X1)
       grind)
    | exact superpose eq151294 eq15
    | (have j1 := eq151294 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq151294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151294
  have eq155660 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152701 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152701
    | exact resolve eq152701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152701
  have eq155995 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155660 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq155660
    | (have j0 := eq155660 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq155660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155660
  have eq160927 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152810 x y
       grind)
    | exact superpose eq152810 eq16
    | (have j1 := eq152810 x y
       grind)
    | exact resolve eq16 eq152810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152810
  have eq162355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq160927
       have i₂ := eq155995 y x
       grind)
    | exact superpose eq155995 eq160927
    | (have j1 := eq155995 (σ x) (σ y)
       grind)
    | (have r₁ := eq160927
       have r₂ := eq155995 y x
       grind)
    | (have r₁ := eq160927
       have r₂ := eq155995 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq160927
       have r₂ := eq155995 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq160927 eq155995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155995 eq160927
  have eq162362 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq162355
  have eq162366 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162362
       grind)
    | exact superpose eq162362 eq16
    | exact resolve eq16 eq162362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162362
  have eq162367 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq162366
       have r₂ := eq821 x
       grind)
    | exact resolve eq162366 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162366
  have eq163634 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162367
       grind)
    | exact superpose eq162367 eq16
    | exact resolve eq16 eq162367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163635 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq162367
       grind)
    | exact superpose eq162367 eq10
    | exact resolve eq10 eq162367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162367
  have eq163904 : x = y := by
    first
    | (have i₁ := eq163635
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq163635
    | exact resolve eq163635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163635
  have eq163905 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq163634
       have i₂ := eq821 x
       grind)
    | exact superpose eq821 eq163634
    | exact resolve eq163634 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq163634
  have eq163920 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq163905
       have i₂ := eq163904
       grind)
    | exact superpose eq163904 eq163905
    | exact resolve eq163905 eq163904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163904 eq163905
  have eq163921 : False := by grind
  exact eq163921

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq190 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq224 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq190
  have eq228 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq224 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq224 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq231 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq228
    | (have j0 := eq228 X0 X1
       grind)
    | exact resolve eq228 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq502 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231
    | exact resolve eq231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq231 (σ X0) X1
       grind)
    | exact superpose eq231 eq15
    | (have j1 := eq231 (σ X0) X1
       grind)
    | exact resolve eq15 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq513
    | (have j0 := eq513 X0 X1
       grind)
    | exact resolve eq513 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq574 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0
       have i₂ := eq502 X1 (τ X0)
       grind)
    | (have i₁ := eq70 X0
       have i₂ := eq502 (τ X0) (τ X0)
       grind)
    | exact superpose eq502 eq70
    | (have j1 := eq502 X1 (τ X0)
       grind)
    | exact resolve eq70 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq582 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq502 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq502 X0 X1
       grind)
    | exact superpose eq502 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq502 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq502 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq502 X0 X0
       grind)
    | exact resolve eq13 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq609 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq598 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq598 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq598 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq640 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq609 X0 (τ X1)
       grind)
    | exact superpose eq609 eq18
    | (have j1 := eq609 X0 (τ X1)
       grind)
    | exact resolve eq18 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq652 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq652 (σ X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq652
    | exact resolve eq652 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3879 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq574
    | exact resolve eq574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq3927 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3879 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq3879
    | (have j0 := eq3879 X0 X1
       grind)
    | exact resolve eq3879 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3879
  have eq4921 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq640 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq640
    | exact resolve eq640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq5017 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4921 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4921
    | (have j0 := eq4921 X0 X1
       grind)
    | exact resolve eq4921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921
  have eq8394 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq524 x y
       grind)
    | exact superpose eq524 eq16
    | (have j1 := eq524 x y
       grind)
    | exact resolve eq16 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8508 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq9441 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8394
       have i₂ := eq3927 x y
       grind)
    | exact superpose eq3927 eq8394
    | (have j1 := eq3927 x y
       grind)
    | exact resolve eq8394 eq3927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3927
  have eq9447 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq8394
       have i₂ := eq5017 y x
       grind)
    | exact superpose eq5017 eq8394
    | (have j1 := eq5017 y x
       grind)
    | (have r₁ := eq8394
       have r₂ := eq5017 y x
       grind)
    | exact resolve eq8394 eq5017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5017
  have eq9448 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq9447
  have eq9454 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq9441
  have eq9459 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9448
       grind)
    | exact superpose eq9448 eq16
    | exact resolve eq16 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9460 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq701 x (σ y)
       have i₂ := eq9448
       grind)
    | exact superpose eq9448 eq701
    | (have j0 := eq701 x (σ y)
       grind)
    | (have r₁ := eq701 x (σ y)
       have r₂ := eq9448
       grind)
    | exact resolve eq701 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq9448
  have eq9469 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq9460
  have eq9474 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9469
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9469
    | exact resolve eq9469 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9469
  have eq9612 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq9474
       have i₂ := eq609 x y
       grind)
    | exact superpose eq609 eq9474
    | (have j1 := eq609 x y
       grind)
    | exact resolve eq9474 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq9614 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8394
       have i₂ := eq9474
       grind)
    | exact superpose eq9474 eq8394
    | exact resolve eq8394 eq9474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8394 eq9474
  have eq9635 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9614
       have r₂ := eq9454
       grind)
    | exact resolve eq9614 eq9454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9454 eq9614
  have eq9636 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have j1 := eq652 x y
       grind)
    | (have r₁ := eq9612
       have r₂ := eq652 x y
       grind)
    | exact resolve eq9612 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq9612
  have eq9637 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq8508 x y
       grind)
    | (have r₁ := eq9635
       have r₂ := eq8508 x y
       grind)
    | exact resolve eq9635 eq8508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8508 eq9635
  have eq9638 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq9636
       have r₂ := eq9459
       grind)
    | exact resolve eq9636 eq9459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9459 eq9636
  have eq9743 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9637
       grind)
    | exact superpose eq9637 eq16
    | exact resolve eq16 eq9637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9637
  have eq9886 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq9743
       have i₂ := eq502 y x
       grind)
    | exact superpose eq502 eq9743
    | (have j1 := eq502 y x
       grind)
    | exact resolve eq9743 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq9887 : (M.op x y) = (k x y) := by grind
  clear eq9886
  have eq9888 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9887
       have i₂ := eq9638
       grind)
    | exact superpose eq9638 eq9887
    | exact resolve eq9887 eq9638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9638 eq9887
  have eq9889 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9743
       have i₂ := eq9888
       grind)
    | exact superpose eq9888 eq9743
    | exact resolve eq9743 eq9888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9743 eq9888
  have eq9901 : False := by grind
  exact eq9901

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq171 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq177 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq335 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq177
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq177 x y
       grind)
    | exact superpose eq177 eq16
    | (have j1 := eq177 x y
       grind)
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq353 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq335
  have eq358 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq353
    | exact resolve eq353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq478 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq341
       have i₂ := eq358 x y
       grind)
    | exact superpose eq358 eq341
    | (have j1 := eq358 (σ x) (σ y)
       grind)
    | (have r₁ := eq341
       have r₂ := eq358 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq341
       have r₂ := eq358 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq341 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq358
  have eq481 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq478
  have eq483 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq481
       grind)
    | exact superpose eq481 eq10
    | exact resolve eq10 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq517 : x = y ∨ x = y := by
    first
    | (have i₁ := eq483
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq483
    | exact resolve eq483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq518 : x = y := by grind
  clear eq517
  have eq567 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq518
       grind)
    | exact superpose eq518 eq16
    | exact resolve eq16 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq568 : False := by grind
  exact eq568

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  have eq28 : x = (τ (σ x)) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq50 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (k X1 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq80
    | (have j1 := eq88 y x
       grind)
    | exact resolve eq80 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq128
       have r₂ := eq27
       grind)
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131
    | exact resolve eq131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq142 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq147 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq51
    | exact resolve eq51 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq27
    | exact resolve eq27 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : (σ (k (k y y) x)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq39 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq39
    | exact resolve eq39 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq88 (σ X0) sF2
       grind)
    | exact superpose eq88 eq39
    | (have j1 := eq88 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq163 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147 eq14
    | exact resolve eq14 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq163 eq147
    | exact resolve eq147 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq165
  have eq174 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq170
       grind)
    | exact resolve eq13 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170 eq14
    | exact resolve eq14 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq176 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq174
  have eq194 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq176 eq93
    | exact resolve eq93 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq198 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq194
    | exact resolve eq194 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq194
  have eq201 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88 y y
       have i₂ := eq198
       grind)
    | exact superpose eq198 eq88
    | (have j0 := eq88 y y
       grind)
    | exact resolve eq88 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq202 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq201
  have eq218 : y = (M.op y (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq14
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq249 : y ≠ y ∨ (M.op (M.op y y) y) = (k y (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y (M.op y y)
       have i₂ := eq218
       grind)
    | exact superpose eq218 eq13
    | (have j0 := eq13 y (M.op y y)
       grind)
    | (have r₁ := eq13 y (M.op y y)
       have r₂ := eq218
       grind)
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq251 : (M.op (M.op y y) y) = (k y (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq249
  have eq316 : (M.op y y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq251
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq251
    | exact resolve eq251 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq317 : (M.op y y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq316
  have eq337 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147 eq52
    | exact resolve eq52 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq349 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq13
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq352
    | exact resolve eq352 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq356 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq346
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq346
    | exact resolve eq346 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq362 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq338
    | exact resolve eq338 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq363 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq52 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq337
    | exact resolve eq337 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq364 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq353
    | exact resolve eq353 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq367 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq362
    | exact resolve eq362 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq368 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq363
    | exact resolve eq363 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq371 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq175 eq356
    | exact resolve eq356 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq356
  have eq376 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq371
  have eq382 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq376
    | exact resolve eq376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq388 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq382 eq163
    | exact resolve eq163 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq397 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq382 eq13
    | exact resolve eq13 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq388
  have eq408 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq397
       have r₂ := eq133
       grind)
    | exact resolve eq397 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq430 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq405 eq52
    | exact resolve eq52 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq437 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51 eq430
    | exact resolve eq430 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq430
  have eq452 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq72
    | (have r₁ := eq72
       have r₂ := eq133
       grind)
    | exact resolve eq72 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq133
  have eq453 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq452
  have eq459 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq408 eq93
    | exact resolve eq93 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq408
  have eq470 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq437 eq14
    | exact resolve eq14 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq517 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq317
       have i₂ := eq459
       grind)
    | exact superpose eq459 eq317
    | exact resolve eq317 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq518 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq198
       have i₂ := eq459
       grind)
    | exact superpose eq459 eq198
    | exact resolve eq198 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq459
  have eq521 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq518
  have eq522 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq517
  have eq549 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op X1 (M.op X0 X0)) X1) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | (have r₁ := eq63 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq63 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq63 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq614 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq549 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq751 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq926 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq382 eq470
    | exact resolve eq470 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq470
  have eq935 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq926
  have eq1503 : ∀ X0 : G, y = (M.op X0 (M.op X0 (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq349 X0 y
       have i₂ := eq522
       grind)
    | exact superpose eq522 eq349
    | exact resolve eq349 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq349 X0 y
       have i₂ := eq202
       grind)
    | exact superpose eq202 eq349
    | exact resolve eq349 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1512 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq935 eq349
    | exact resolve eq349 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq1646 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq240
    | exact resolve eq240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq240 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq240
    | (have j0 := eq240 X0 y
       grind)
    | exact resolve eq240 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq4719 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq364 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq364
    | exact resolve eq364 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq5030 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq349 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq349 eq4719
    | exact resolve eq4719 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq6180 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq614 (M.op x x)
       have i₂ := eq349 (M.op x x) x
       grind)
    | exact superpose eq349 eq614
    | exact resolve eq614 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq6195 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1512 eq614
    | exact resolve eq614 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq1512
  have eq6339 : (σ (k (k y y) x)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq159 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq159
    | exact resolve eq159 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq7520 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X1 (M.op X1 X0)
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq367
    | exact resolve eq367 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq7607 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7520 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq7520
    | exact resolve eq7520 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq7520
  have eq7737 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7607 X0 X1
       have i₂ := eq368 X0 X1
       grind)
    | exact superpose eq368 eq7607
    | exact resolve eq7607 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq7607
  have eq8073 : y ≠ (M.op x (M.op x y)) ∨ y = (k (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq50 eq351
    | exact resolve eq351 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq351
  have eq13304 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq521 eq1646
    | exact resolve eq1646 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq1646
  have eq13349 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13304 X0
       have i₂ := eq1659 X0
       grind)
    | exact superpose eq1659 eq13304
    | exact resolve eq13304 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13304
  have eq15236 : (M.op y (τ (M.op (σ x) (σ y)))) = (k (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6180 y
       have i₂ := eq522
       grind)
    | exact superpose eq522 eq6180
    | exact resolve eq6180 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6180
  have eq15267 : (M.op y (τ (M.op (σ x) (σ y)))) = (τ (k (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15236
       have i₂ := eq1659 sF4
       grind)
    | exact superpose eq1659 eq15236
    | exact resolve eq15236 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq15236
  have eq15492 : (τ (M.op (σ x) (σ y))) = (M.op (M.op y (τ (M.op (σ x) (σ y)))) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7737 y y
       have i₂ := eq522
       grind)
    | exact superpose eq522 eq7737
    | exact resolve eq7737 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq7737
  have eq34810 : (τ (k (M.op (σ x) (σ y)) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6195 eq13349
    | exact resolve eq13349 eq6195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195 eq13349
  have eq34894 : (τ (k (M.op (σ x) (σ y)) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq34810
  have eq70591 : y = (M.op (M.op y (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15492 eq1504
    | exact resolve eq1504 eq15492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504 eq15492
  have eq70605 : y = (M.op (M.op y (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq70591
  have eq99062 : y = (M.op (M.op y (τ (M.op (σ x) (σ y)))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70605 eq1503
    | exact resolve eq1503 eq70605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq70605
  have eq99077 : y = (M.op (M.op y (τ (M.op (σ x) (σ y)))) y) ∨ y = (M.op x y) := by grind
  clear eq99062
  have eq99094 : y = (M.op (τ (k (M.op (σ x) (σ y)) (σ y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15267 eq99077
    | exact resolve eq99077 eq15267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15267 eq99077
  have eq99127 : y = (M.op (τ (k (M.op (σ x) (σ y)) (σ y))) y) ∨ y = (M.op x y) := by grind
  clear eq99094
  have eq99157 : y = (M.op (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34894 eq99127
    | exact resolve eq99127 eq34894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34894 eq99127
  have eq99192 : y = (M.op (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) y) ∨ y = (M.op x y) := by grind
  clear eq99157
  have eq151472 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq453 eq120
    | exact resolve eq120 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq453
  have eq151486 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq151472
  have eq151491 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq151486
       have r₂ := eq148
       grind)
    | exact resolve eq151486 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq151486
  have eq151505 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151491 eq5030
    | exact resolve eq5030 eq151491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5030 eq151491
  have eq151512 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54 eq151505
    | exact resolve eq151505 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq151505
  have eq153059 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151512 eq99192
    | exact resolve eq99192 eq151512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99192 eq151512
  have eq153123 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) := by grind
  clear eq153059
  have eq153226 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq153123
    | exact resolve eq153123 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq153123
  have eq153248 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq153226
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq153226
    | exact resolve eq153226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153226
  have eq153249 : y = (M.op x y) := by grind
  clear eq153248
  have eq153250 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq153249 eq20
    | exact resolve eq20 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq153255 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq153249 eq70
    | (have r₁ := eq70
       have r₂ := eq153249
       grind)
    | exact resolve eq70 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq153401 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq153249 eq8073
    | exact resolve eq8073 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073
  have eq153404 : y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq153255
  have eq153407 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq153401
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq153401
    | exact resolve eq153401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153401
  have eq153542 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq153250
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq153250
    | exact resolve eq153250 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153250
  have eq153544 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq153407
       have r₂ := eq153249
       grind)
    | exact resolve eq153407 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153407
  have eq153552 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq153544
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq153544
    | exact resolve eq153544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153544
  have eq153557 : y = (k y y) := by
    first
    | exact superpose eq153249 eq153552
    | exact resolve eq153552 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153552
  have eq153565 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq153542 eq26
    | exact resolve eq26 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq155126 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq153557
       grind)
    | exact superpose eq153557 eq81
    | exact resolve eq81 eq153557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq153557
  have eq155208 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq153542 eq155126
    | exact resolve eq155126 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155126
  have eq155233 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq155208
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq155208
    | exact resolve eq155208 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155208
  have eq155252 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq153542 eq155233
    | exact resolve eq155233 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155233
  have eq166276 : (σ (k (k y y) x)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq153542 eq6339
    | exact resolve eq6339 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq166277 : (σ (k (k y y) x)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq155252 eq166276
    | exact resolve eq166276 eq155252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166276
  have eq166278 : (M.op (σ x) (σ y)) = (σ (k (k y y) x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq153565 eq166277
    | exact resolve eq166277 eq153565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166277
  have eq166279 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq166278
       have i₂ := eq154
       grind)
    | exact superpose eq154 eq166278
    | exact resolve eq166278 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq166278
  have eq166280 : (M.op (σ x) (σ y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq153542 eq166279
    | exact resolve eq166279 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166279
  have eq166281 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | exact superpose eq155252 eq166280
    | exact resolve eq166280 eq155252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166280
  have eq166282 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq153542 eq166281
    | exact resolve eq166281 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166281
  have eq166283 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq155252 eq166282
    | exact resolve eq166282 eq155252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155252 eq166282
  have eq166284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq153565 eq166283
    | exact resolve eq166283 eq153565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153565 eq166283
  have eq166285 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq166284
       have r₂ := eq27
       grind)
    | exact resolve eq166284 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166284
  have eq166290 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq166285 eq751
    | exact resolve eq751 eq166285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq166285
  have eq166313 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq153249 eq166290
    | exact resolve eq166290 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166290
  have eq170550 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq153404
       have i₂ := eq166313
       grind)
    | exact superpose eq166313 eq153404
    | exact resolve eq153404 eq166313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153404
  have eq170553 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq170550
       grind)
    | exact superpose eq170550 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq170550
       grind)
    | exact resolve eq13 eq170550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170550
  have eq170568 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq170553
  have eq170580 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq170568
       have i₂ := eq166313
       grind)
    | exact superpose eq166313 eq170568
    | exact resolve eq170568 eq166313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166313 eq170568
  have eq170587 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq170580
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq170580
    | exact resolve eq170580 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq170580
  have eq170594 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq153249 eq170587
    | exact resolve eq170587 eq153249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153249 eq170587
  have eq170595 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq170594
  have eq170660 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq170595 eq15
    | exact resolve eq15 eq170595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170595
  have eq171059 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq170660
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq170660
    | exact resolve eq170660 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq170660
  have eq171119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153542 eq171059
    | exact resolve eq171059 eq153542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153542 eq171059
  have eq171157 : False := by grind
  exact eq171157

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  clear eq36
  have eq47 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq62
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq67
    | exact resolve eq67 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq292 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq298 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq300 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq49 (M.op X1 X1) X0
       grind)
    | exact superpose eq49 eq303
    | exact resolve eq303 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq306 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq298
       have i₂ := eq49 sF4 sF4
       grind)
    | exact superpose eq49 eq298
    | exact resolve eq298 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq308 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq295
       have i₂ := eq49 sF0 sF0
       grind)
    | exact superpose eq49 eq295
    | exact resolve eq295 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq310 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq49 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq49 eq292
    | exact resolve eq292 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq311 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq49 X1 X1
       grind)
    | exact superpose eq49 eq304
    | exact resolve eq304 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq315 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq310
    | exact resolve eq310 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq300 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq300 (M.op X0 X0) X0
       grind)
    | exact superpose eq300 eq300
    | exact resolve eq300 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq613 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq306 eq49
    | exact resolve eq49 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq618 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq613
       have i₂ := eq49 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq49 eq613
    | exact resolve eq613 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq620 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq618
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq618
    | exact resolve eq618 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq621 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq620
       have i₂ := eq49 sF3 sF3
       grind)
    | exact superpose eq49 eq620
    | exact resolve eq620 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq622 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq621 eq300
    | exact resolve eq300 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq638 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq308 eq49
    | exact resolve eq49 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq643 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq638
       have i₂ := eq49 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq49 eq638
    | exact resolve eq638 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq645 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq643
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq643
    | exact resolve eq643 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq646 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq645
       have i₂ := eq49 y y
       grind)
    | exact superpose eq49 eq645
    | exact resolve eq645 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq647 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq300 y y
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq300
    | exact resolve eq300 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq3079 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq315 X0 X1
       grind)
    | exact superpose eq315 eq49
    | exact resolve eq49 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq3086 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3079 X0 X1
       have i₂ := eq49 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq49 eq3079
    | exact resolve eq3079 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079
  have eq3126 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3086 X0 X1
       have i₂ := eq49 (M.op X0 X0) X1
       grind)
    | exact superpose eq49 eq3086
    | exact resolve eq3086 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3158 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3126 X0 X1
       have i₂ := eq49 X0 X0
       grind)
    | exact superpose eq49 eq3126
    | exact resolve eq3126 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3126
  have eq3178 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3158 X0 X1
       have i₂ := eq311 X1 X0
       grind)
    | exact superpose eq311 eq3158
    | exact resolve eq3158 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq3158
  have eq3725 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3178 X1 X2
       have i₂ := eq3178 X1 X0
       grind)
    | (have i₁ := eq3178 X0 X1
       have i₂ := eq3178 X0 X0
       grind)
    | exact superpose eq3178 eq3178
    | exact resolve eq3178 eq3178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq4800 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq647 eq3725
    | exact resolve eq3725 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq4811 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq622 eq3725
    | exact resolve eq3725 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq3725
  have eq10591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq69 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10591
    | exact resolve eq10591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10591
  have eq10598 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10592
       have r₂ := eq28
       grind)
    | exact resolve eq10592 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10592
  have eq10600 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10598
    | exact resolve eq10598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10598
  have eq10614 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10600 eq320
    | exact resolve eq320 eq10600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10600
  have eq10638 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10614
    | exact resolve eq10614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10614
  have eq10639 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10638
  have eq10652 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq320 y
       have i₂ := eq10639
       grind)
    | exact superpose eq10639 eq320
    | exact resolve eq320 eq10639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10639
  have eq10676 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10652
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10652
    | exact resolve eq10652 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10652
  have eq10677 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10676
  have eq10678 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10677 eq28
    | exact resolve eq28 eq10677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10692 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10677 eq4811
    | exact resolve eq4811 eq10677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4811 eq10677
  have eq10694 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10692 x
       have i₂ := eq300 x sF2
       grind)
    | exact superpose eq300 eq10692
    | exact resolve eq10692 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10692
  have eq10815 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10694
  have eq10961 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10815 eq69
    | exact resolve eq69 eq10815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq10815
  have eq10974 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq10961
  have eq10981 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10974
       have r₂ := eq10678
       grind)
    | exact resolve eq10974 eq10678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10678 eq10974
  have eq11151 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq320 y
       have i₂ := eq10981
       grind)
    | exact superpose eq10981 eq320
    | exact resolve eq320 eq10981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10981
  have eq11175 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11151
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11151
    | exact resolve eq11151 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq11151
  have eq11176 : x = (M.op x y) := by grind
  clear eq11175
  have eq11177 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11176 eq21
    | exact resolve eq21 eq11176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq11240 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) := by
    intro X0
    first
    | exact superpose eq11176 eq4800
    | exact resolve eq4800 eq11176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4800 eq11176
  have eq11242 : x = (M.op y y) := by
    first
    | (have i₁ := eq11240 x
       have i₂ := eq300 x x
       grind)
    | exact superpose eq300 eq11240
    | exact resolve eq11240 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq11240
  have eq11295 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11177
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11177
    | exact resolve eq11177 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11177
  have eq11456 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11295 eq27
    | exact resolve eq27 eq11295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11527 : x = (k x y) := by grind
  clear eq11242
  have eq12020 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq461 x y
       have i₂ := eq11527
       grind)
    | exact superpose eq11527 eq461
    | (have j0 := eq461 x y
       grind)
    | exact resolve eq461 eq11527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq11527
  have eq12023 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq12020
  have eq12026 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12023
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12023
    | exact resolve eq12023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023
  have eq12037 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12026
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12026
    | exact resolve eq12026 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12026
  have eq12048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12037
    | exact resolve eq12037 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12037
  have eq12057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11295 eq12048
    | exact resolve eq12048 eq11295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12048
  have eq12061 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq12057
       have r₂ := eq28
       grind)
    | exact resolve eq12057 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12057
  have eq12065 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12061
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12061
    | exact resolve eq12061 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12061
  have eq12068 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12065
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12065
    | exact resolve eq12065 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12065
  have eq12071 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11295 eq12068
    | exact resolve eq12068 eq11295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11295 eq12068
  have eq12118 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12071 eq320
    | exact resolve eq320 eq12071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq12071
  have eq12142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11456 eq12118
    | exact resolve eq12118 eq11456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456 eq12118
  have eq12153 : False := by grind
  exact eq12153

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq29
    | (have j0 := eq29 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq71 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq71 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq71 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1007 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq991
  have eq1131 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq16
    | exact resolve eq16 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1007
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1007
       grind)
    | exact resolve eq13 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1138 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1136
  have eq1139 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1138
  have eq1142 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1139
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1139
    | exact resolve eq1139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq4043 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq567 y x
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq567
    | (have j0 := eq567 y x
       grind)
    | exact resolve eq567 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq4045 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq10
    | exact resolve eq10 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq4067 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq4043
  have eq4076 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4045
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4045
    | exact resolve eq4045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4045
  have eq4077 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4067
       have r₂ := eq1131
       grind)
    | exact resolve eq4067 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq4067
  have eq4080 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq4076
       have r₂ := eq13 y x
       grind)
    | exact resolve eq4076 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq9526 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29 x y
       have i₂ := eq4080
       grind)
    | exact superpose eq4080 eq29
    | (have j0 := eq29 x y
       grind)
    | exact resolve eq29 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4080
  have eq9529 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9526
  have eq80000 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq9529
       grind)
    | exact superpose eq9529 eq16
    | exact resolve eq16 eq9529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9529
  have eq93658 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq80000
       have i₂ := eq4077
       grind)
    | exact superpose eq4077 eq80000
    | exact resolve eq80000 eq4077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4077 eq80000
  have eq93659 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq93658
  have eq93660 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq93659
  have eq106248 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq93660
       grind)
    | exact superpose eq93660 eq10
    | exact resolve eq10 eq93660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93660
  have eq106454 : x = y ∨ x = y := by
    first
    | (have i₁ := eq106248
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq106248
    | exact resolve eq106248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106248
  have eq106455 : x = y := by grind
  clear eq106454
  have eq115855 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106455
       grind)
    | exact superpose eq106455 eq16
    | exact resolve eq16 eq106455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106455
  have eq115856 : False := by grind
  exact eq115856

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq114 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq152 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq114
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq152
  have eq165 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq167 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq165
  have eq207 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq47
    | exact resolve eq47 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) := by grind
  have eq368 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq49 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq50 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq49 X0 x x X3
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq634 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (σ X0) X1 X2 X3
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq49
    | (have j1 := eq63 X0 X0
       grind)
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq647 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq634 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1645 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq396 X0 X0 X0
       grind)
    | exact superpose eq396 eq14
    | exact resolve eq14 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1647 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 X0))
       have i₂ := eq396 X0 X0 X0
       grind)
    | exact superpose eq396 eq47
    | exact resolve eq47 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op X0 (M.op X0 X0))
       have i₂ := eq396 X0 X0 X0
       grind)
    | exact superpose eq396 eq48
    | exact resolve eq48 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq1893 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq1647 X0
       grind)
    | exact superpose eq1647 eq368
    | exact resolve eq368 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq1923 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1647 eq369
    | exact resolve eq369 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1936 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq369 eq1923
    | exact resolve eq1923 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1973 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq47 eq1893
    | exact resolve eq1893 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1975 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq210 eq1893
    | exact resolve eq1893 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq1893
  have eq2134 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1648 eq369
    | exact resolve eq369 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq2147 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq369 eq2134
    | exact resolve eq2134 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq2134
  have eq11151 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ (k y y))) (M.op (σ y) (M.op X2 X2))) = X2 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 y X0 X1 X2
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq647
    | (have j0 := eq647 y X0 X1 X2
       grind)
    | exact resolve eq647 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq11227 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (k (σ y) (σ y))) (M.op (σ y) (M.op X2 X2))) = X2 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11151 X0 X1 X2
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq11151
    | exact resolve eq11151 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11151
  have eq17655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17655
    | exact resolve eq17655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17655
  have eq17667 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17656
       have r₂ := eq28
       grind)
    | exact resolve eq17656 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17656
  have eq17669 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17667
    | exact resolve eq17667 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667
  have eq17702 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17669 eq1973
    | exact resolve eq1973 eq17669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17669
  have eq17742 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17702
    | exact resolve eq17702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17702
  have eq17743 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17742
  have eq17779 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1973 y
       have i₂ := eq17743
       grind)
    | exact superpose eq17743 eq1973
    | exact resolve eq1973 eq17743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17743
  have eq17824 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17779
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17779
    | exact resolve eq17779 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17779
  have eq17825 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17824
  have eq17830 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17825 eq28
    | exact resolve eq28 eq17825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17831 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17825 eq48
    | exact resolve eq48 eq17825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq17860 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17825 eq2147
    | exact resolve eq2147 eq17825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq17864 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17860
    | exact resolve eq17860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860
  have eq17985 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  have eq18073 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17825 eq17985
    | exact resolve eq17985 eq17825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17985
  have eq18079 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18073
  have eq18206 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18079 eq98
    | exact resolve eq98 eq18079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq18079
  have eq18217 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18206
  have eq19506 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1973 y
       have i₂ := eq18217
       grind)
    | exact superpose eq18217 eq1973
    | exact resolve eq1973 eq18217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973 eq18217
  have eq19551 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19506
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19506
    | exact resolve eq19506 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19506
  have eq19552 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19551
  have eq19559 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19552 eq30
    | exact resolve eq30 eq19552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq19725 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq19559
    | exact resolve eq19559 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19559
  have eq19816 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq20050 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq207 eq160
    | exact resolve eq160 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq20051 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq207 eq20050
    | exact resolve eq20050 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq20050
  have eq25455 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17864 eq17831
    | exact resolve eq17831 eq17864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17831 eq17864
  have eq25497 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq25455
  have eq25534 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17825 eq25497
    | exact resolve eq25497 eq17825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17825 eq25497
  have eq25570 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq25534
  have eq25593 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq25570 eq49
    | exact resolve eq49 eq25570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq25570
  have eq25640 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25593 x x
       have i₂ := eq430 sF3 (M.op x x)
       grind)
    | exact superpose eq430 eq25593
    | exact resolve eq25593 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq25593
  have eq30564 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq415 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1645 X0 X0 X1
       grind)
    | exact superpose eq1645 eq415
    | exact resolve eq415 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq30641 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30564 X0 X1 x x x
       have i₂ := eq415 X0 X0 x x x
       grind)
    | exact superpose eq415 eq30564
    | exact resolve eq30564 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq30564
  have eq35641 : (M.op y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20051 eq16
    | exact resolve eq16 eq20051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20051
  have eq35697 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq155 eq35641
    | exact resolve eq35641 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35641
  have eq266592 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11227 eq371
    | exact resolve eq371 eq11227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq11227
  have eq3303617 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25640 eq167
    | exact resolve eq167 eq25640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq25640
  have eq3304225 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3303617
    | exact resolve eq3303617 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303617
  have eq3304245 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq3304225
       grind)
    | exact superpose eq3304225 eq86
    | exact resolve eq86 eq3304225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3304225
  have eq3304723 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3304245
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3304245
    | exact resolve eq3304245 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304245
  have eq3305220 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19552 eq3304723
    | exact resolve eq3304723 eq19552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19552 eq3304723
  have eq3305497 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3305220
  have eq3305562 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3305497
       have r₂ := eq17830
       grind)
    | exact resolve eq3305497 eq17830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17830 eq3305497
  have eq3305603 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3305562 eq155
    | exact resolve eq155 eq3305562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq3305562
  have eq3305911 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3305603
    | exact resolve eq3305603 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3305603
  have eq3306576 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq35697 eq3305911
    | exact resolve eq3305911 eq35697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35697
  have eq3467233 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq3306576 eq212
    | exact resolve eq212 eq3306576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq3306576
  have eq3518509 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq3467233 eq3305911
    | exact resolve eq3305911 eq3467233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305911 eq3467233
  have eq3518802 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3518509
  have eq3519401 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3518802 eq1975
    | exact resolve eq1975 eq3518802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975 eq3518802
  have eq3520430 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19725 eq3519401
    | exact resolve eq3519401 eq19725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19725 eq3519401
  have eq3521123 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3520430
       have r₂ := eq19816
       grind)
    | exact resolve eq3520430 eq19816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19816 eq3520430
  have eq3521213 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3521123
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3521123
    | exact resolve eq3521123 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521123
  have eq3521214 : x = (M.op x y) := by grind
  clear eq3521213
  have eq3522408 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3521214 eq21
    | exact resolve eq21 eq3521214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3522524 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3521214 eq1936
    | exact resolve eq1936 eq3521214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq3523086 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3522524
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3522524
    | exact resolve eq3522524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3522524
  have eq3523157 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3522408
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3522408
    | exact resolve eq3522408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522408
  have eq3523232 : x = (M.op y y) := by
    first
    | exact superpose eq3521214 eq3523086
    | exact resolve eq3523086 eq3521214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521214 eq3523086
  have eq3523264 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3523157 eq27
    | exact resolve eq27 eq3523157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3525148 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq3523232
       grind)
    | exact superpose eq3523232 eq105
    | exact resolve eq105 eq3523232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq3525220 : y = (k y x) := by grind
  clear eq3523232
  have eq3526426 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3525148
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3525148
    | exact resolve eq3525148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525148
  have eq3526736 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3523157 eq3526426
    | exact resolve eq3526426 eq3523157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526426
  have eq3528206 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq3525220
       grind)
    | exact superpose eq3525220 eq85
    | exact resolve eq85 eq3525220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq3525220
  have eq3528371 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq3523157 eq3528206
    | exact resolve eq3528206 eq3523157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528206
  have eq3528421 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3528371
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3528371
    | exact resolve eq3528371 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528371
  have eq3528678 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3528421 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq3528421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528421
  have eq3528722 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3523264 eq3528678
    | exact resolve eq3528678 eq3523264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528678
  have eq3528744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3523264 eq3528722
    | exact resolve eq3528722 eq3523264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528722
  have eq3528764 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3528744
       have r₂ := eq28
       grind)
    | exact resolve eq3528744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528744
  have eq3563301 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3528764 eq30641
    | exact resolve eq30641 eq3528764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30641 eq3528764
  have eq3563505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3523264 eq3563301
    | exact resolve eq3563301 eq3523264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563301
  have eq3564035 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3563505
       have r₂ := eq28
       grind)
    | exact resolve eq3563505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563505
  have eq3564628 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq3564035 eq28
    | exact resolve eq28 eq3564035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4421213 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3526736 eq266592
    | exact resolve eq266592 eq3526736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266592
  have eq4421791 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3523264 eq4421213
    | exact resolve eq4421213 eq3523264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523264 eq4421213
  have eq4421794 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3564035 eq4421791
    | exact resolve eq4421791 eq3564035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564035 eq4421791
  have eq4421795 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq4421794
  have eq4422077 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq4421795
  have eq4424369 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq4422077 eq3526736
    | exact resolve eq3526736 eq4422077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526736 eq4422077
  have eq4424613 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq4424369
  have eq4424710 : x = y := by
    first
    | (have r₁ := eq4424613
       have r₂ := eq3564628
       grind)
    | exact resolve eq4424613 eq3564628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4424613
  have eq4424873 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4424710
       grind)
    | exact superpose eq4424710 eq25
    | exact resolve eq25 eq4424710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4424710
  have eq4426702 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4424873
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4424873
    | exact resolve eq4424873 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4424873
  have eq4426997 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3523157 eq4426702
    | exact resolve eq4426702 eq3523157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523157 eq4426702
  have eq4427157 : False := by grind
  exact eq4427157
