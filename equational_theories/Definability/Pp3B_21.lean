import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq62 X2 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X2 (M.op X0 X1))
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq98 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq102 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq105 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq131 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq444 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq435 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq435
    | (have j0 := eq435 (τ X0)
       grind)
    | exact resolve eq435 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq435
  have eq445 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq444 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq444
    | (have j0 := eq444 X0
       grind)
    | exact resolve eq444 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq448 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq445
    | (have j0 := eq445 X0
       grind)
    | exact resolve eq445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq480 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq12
    | (have j1 := eq105 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq105 X0
       grind)
    | exact resolve eq12 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq500 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq489 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq501 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq500 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq500
    | (have j0 := eq500 X0
       grind)
    | exact resolve eq500 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq502 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq480
    | (have j0 := eq480 X0
       grind)
    | exact resolve eq480 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq508 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq502 X0
       grind)
    | exact superpose eq502 eq12
    | (have j1 := eq502 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq502 X0
       grind)
    | exact resolve eq12 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq538 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq10
    | (have j1 := eq527 X0
       grind)
    | exact resolve eq10 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (k X0 X0)
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq23
    | (have j1 := eq527 X0
       grind)
    | exact resolve eq23 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq565 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X1
       have i₂ := eq23 X1 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq545
    | (have j0 := eq545 X0 X1
       grind)
    | exact resolve eq545 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq572 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq538
    | (have j0 := eq538 X0
       grind)
    | exact resolve eq538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq590 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131 x y
       grind)
    | exact superpose eq131 eq16
    | (have j1 := eq131 x y
       grind)
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq631 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq903 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq501 X0
       grind)
    | exact superpose eq501 eq11
    | (have j1 := eq501 X0
       grind)
    | exact resolve eq11 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq905 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq903
    | (have j0 := eq903 X0
       grind)
    | exact resolve eq903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq952 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq905 X0
       grind)
    | exact superpose eq905 eq10
    | (have j1 := eq905 X0
       grind)
    | exact resolve eq10 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq997 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X0) = (M.op (M.op X1 (τ X0)) (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (τ X0) (τ X0)
       have i₂ := eq952 X0
       grind)
    | exact superpose eq952 eq62
    | (have j1 := eq952 X0
       grind)
    | exact resolve eq62 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X0) = (M.op (τ (k X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) (τ X0) X1
       have i₂ := eq952 X0
       grind)
    | exact superpose eq952 eq62
    | (have j1 := eq952 X0
       grind)
    | exact resolve eq62 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1623 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq997 (σ X0) X1
       grind)
    | exact superpose eq997 eq29
    | (have j1 := eq997 (σ X0) X1
       grind)
    | exact resolve eq29 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1637 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1623
    | (have j0 := eq1623 X0 X1
       grind)
    | exact resolve eq1623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1655 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1637 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1637
    | (have j0 := eq1637 X0 X1
       grind)
    | exact resolve eq1637 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1672 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1655 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1655
    | (have j0 := eq1655 X0 X1
       grind)
    | exact resolve eq1655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1698 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0
       have i₂ := eq1672 X0 X1
       grind)
    | exact superpose eq1672 eq448
    | (have j0 := eq448 X0
       have j1 := eq1672 X0 X1
       grind)
    | (have r₁ := eq448 X0
       have r₂ := eq1672 X0 X1
       grind)
    | exact resolve eq448 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1719 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1789 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq62 (M.op x X0) (k X0 X0) X2
       have i₂ := eq1719 X0 x
       grind)
    | exact superpose eq1719 eq62
    | (have j1 := eq1719 X0 x
       grind)
    | exact resolve eq62 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1926 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (k (σ X0) (σ X0))) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq998 (σ X0) X1
       grind)
    | exact superpose eq998 eq29
    | (have j1 := eq998 (σ X0) X1
       grind)
    | exact resolve eq29 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq998
  have eq1940 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (k (σ X0) (σ X0))) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1926 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1926
    | (have j0 := eq1926 X0 X1
       grind)
    | exact resolve eq1926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq1958 : ∀ X0 X1 : G, (M.op (τ (k (σ X0) (σ X0))) (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1940 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1940
    | (have j0 := eq1940 X0 X1
       grind)
    | exact resolve eq1940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq1975 : ∀ X0 X1 : G, (M.op (k (τ (σ X0)) X0) (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1958 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1958
    | (have j0 := eq1958 X0 X1
       grind)
    | exact resolve eq1958 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1958
  have eq1990 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1975 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1975
    | (have j0 := eq1975 X0 X1
       grind)
    | exact resolve eq1975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2024 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1990 X0 (M.op (k X0 X0) x)
       have i₂ := eq1789 X0 x
       grind)
    | exact superpose eq1789 eq1990
    | (have j0 := eq1990 X0 x
       have j1 := eq1789 X0 x
       grind)
    | exact resolve eq1990 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq2038 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (k X0 X0) (M.op X0 x)
       have i₂ := eq1990 X0 x
       grind)
    | exact superpose eq1990 eq62
    | (have j1 := eq1990 X0 X1
       grind)
    | exact resolve eq62 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq2059 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2024 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq2024 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq2024 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2095 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) = (σ (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq502 (k X0 X0)
       have i₂ := eq2059 X0
       grind)
    | exact superpose eq2059 eq502
    | (have j1 := eq2059 X0
       grind)
    | exact resolve eq502 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq2059
  have eq2096 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2224 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1719 X0 (M.op x (k X0 X0))
       have i₂ := eq2038 X0 x
       grind)
    | exact superpose eq2038 eq1719
    | (have j0 := eq1719 X0 x
       have j1 := eq2038 X0 x
       grind)
    | exact resolve eq1719 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719 eq2038
  have eq2229 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2224 X0
       have j1 := eq448 X0
       grind)
    | (have r₁ := eq2224 X0
       have r₂ := eq448 X0
       grind)
    | exact resolve eq2224 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq2224
  have eq2441 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) (k X0 X0))
       have i₂ := eq2096 X0
       grind)
    | exact superpose eq2096 eq10
    | (have j1 := eq2096 X0
       grind)
    | exact resolve eq10 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2481 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2441 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2441
    | (have j0 := eq2441 X0
       grind)
    | exact resolve eq2441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2487 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq2542 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2487 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq4365 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq4432 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4365 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4365
    | (have j0 := eq4365 X0 X1
       grind)
    | exact resolve eq4365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq13171 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq565
    | (have j0 := eq565 X1 X1
       grind)
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq13235 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (k X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X1
       have i₂ := eq13171 X0 X1
       grind)
    | exact superpose eq13171 eq2229
    | (have j0 := eq2229 X0
       have j1 := eq13171 X1 X0
       grind)
    | exact resolve eq2229 eq13171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq13171
  have eq13290 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13235
  have eq13497 : ∀ X0 : G, (k (k X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2481 X0
       have i₂ := eq13290 X0 (k X0 X0)
       grind)
    | exact superpose eq13290 eq2481
    | (have j0 := eq2481 X0
       have j1 := eq13290 X0 x
       grind)
    | exact resolve eq2481 eq13290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq13290
  have eq13517 : ∀ X0 : G, (k (k X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13497 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq13497 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq13497 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq13497
  have eq13643 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13517 (M.op X0 X0)
       have i₂ := eq2542 X0
       grind)
    | exact superpose eq2542 eq13517
    | (have j1 := eq2542 X0
       grind)
    | exact resolve eq13517 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq13517
  have eq13699 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13643
  have eq13734 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq13699 X0
       have j1 := eq95 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13699 x
       have r₂ := eq95 x x x
       grind)
    | exact resolve eq13699 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq13699
  have eq13768 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13734 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq13734 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq13734
    | exact resolve eq13734 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13734
  have eq13904 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq13768 (σ X0)
       grind)
    | exact superpose eq13768 eq15
    | exact resolve eq15 eq13768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13934 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13904 X0
       have i₂ := eq13768 X0
       grind)
    | exact superpose eq13768 eq13904
    | exact resolve eq13904 eq13768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13768 eq13904
  have eq18743 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq603 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq603
    | (have j0 := eq603 (τ X0) (τ X1)
       grind)
    | exact resolve eq603 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq18770 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18743 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq18743
    | (have j0 := eq18743 X0 X1
       grind)
    | exact resolve eq18743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18743
  have eq18779 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18770 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18770
    | (have j0 := eq18770 X0 X1
       grind)
    | exact resolve eq18770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18770
  have eq18785 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18779 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18779
    | (have j0 := eq18779 X0 X1
       grind)
    | exact resolve eq18779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18779
  have eq18788 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18785 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18785
    | (have j0 := eq18785 X0 X1
       grind)
    | exact resolve eq18785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18785
  have eq18791 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18788 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18788
    | (have j0 := eq18788 X0 X1
       grind)
    | exact resolve eq18788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18788
  have eq18794 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18791 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18791
    | (have j0 := eq18791 X0 X1
       grind)
    | exact resolve eq18791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18791
  have eq51101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq590
       have i₂ := eq4432 x y
       grind)
    | exact superpose eq4432 eq590
    | (have j1 := eq4432 (σ x) (σ y)
       grind)
    | (have r₁ := eq590
       have r₂ := eq4432 x y
       grind)
    | (have r₁ := eq590
       have r₂ := eq4432 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq590
       have r₂ := eq4432 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq590 eq4432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4432
  have eq51102 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq51101
  have eq282170 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51102
       grind)
    | exact superpose eq51102 eq16
    | exact resolve eq16 eq51102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51102
  have eq282171 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq282170
       have r₂ := eq13934 x
       grind)
    | exact resolve eq282170 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282170
  have eq282174 : y ≠ y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq282171
       grind)
    | exact superpose eq282171 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq282171
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq282171
       grind)
    | exact resolve eq12 eq282171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282176 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y X0
       have i₂ := eq282171
       grind)
    | exact superpose eq282171 eq62
    | exact resolve eq62 eq282171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282171
  have eq282219 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq282174
  have eq282333 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq282176 (M.op y x)
       have i₂ := eq282176 x
       grind)
    | exact superpose eq282176 eq282176
    | exact resolve eq282176 eq282176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282176
  have eq282392 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq282333
  have eq282460 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq62 (σ x) (σ y) X0
       have i₂ := eq282392
       grind)
    | exact superpose eq282392 eq62
    | exact resolve eq62 eq282392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq282392
  have eq294926 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq282219
       grind)
    | exact superpose eq282219 eq603
    | (have j0 := eq603 x y
       grind)
    | exact resolve eq603 eq282219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq282219
  have eq294943 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq294926
  have eq295246 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq282460 (M.op (σ y) x)
       have i₂ := eq282460 x
       grind)
    | exact superpose eq282460 eq282460
    | exact resolve eq282460 eq282460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282460
  have eq295354 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq295246
  have eq295392 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq295354
       have i₂ := eq13934 y
       grind)
    | exact superpose eq13934 eq295354
    | exact resolve eq295354 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295354
  have eq295418 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq295392
       grind)
    | exact superpose eq295392 eq10
    | exact resolve eq10 eq295392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295392
  have eq295658 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq295418
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq295418
    | exact resolve eq295418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295418
  have eq295725 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq295658
       grind)
    | exact superpose eq295658 eq16
    | exact resolve eq16 eq295658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295658
  have eq295801 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq295725
       have r₂ := eq13934 x
       grind)
    | exact resolve eq295725 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295725
  have eq295852 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq295801
       grind)
    | exact superpose eq295801 eq10
    | exact resolve eq10 eq295801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295801
  have eq296139 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq295852
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq295852
    | exact resolve eq295852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295852
  have eq296140 : y = (M.op y y) := by grind
  clear eq296139
  have eq296216 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq294943
       have i₂ := eq296140
       grind)
    | exact superpose eq296140 eq294943
    | exact resolve eq294943 eq296140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294943
  have eq296367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq296216
  have eq300589 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq296367
       grind)
    | exact superpose eq296367 eq16
    | exact resolve eq16 eq296367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300638 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq296367
       grind)
    | exact superpose eq296367 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq296367
       grind)
    | exact resolve eq12 eq296367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296367
  have eq300686 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq300638
  have eq300706 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq300686
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq300686
    | exact resolve eq300686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300686
  have eq300748 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq300706
       have i₂ := eq13934 y
       grind)
    | exact superpose eq13934 eq300706
    | exact resolve eq300706 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300706
  have eq300763 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq300748
       have i₂ := eq296140
       grind)
    | exact superpose eq296140 eq300748
    | exact resolve eq300748 eq296140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296140 eq300748
  have eq300782 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq300763
       grind)
    | exact superpose eq300763 eq10
    | exact resolve eq10 eq300763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300763
  have eq301046 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq300782
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq300782
    | exact resolve eq300782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300782
  have eq301148 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301046
       grind)
    | exact superpose eq301046 eq16
    | exact resolve eq16 eq301046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301046
  have eq301233 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq301148
       have r₂ := eq13934 x
       grind)
    | exact resolve eq301148 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301148
  have eq301263 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq301233
       grind)
    | exact superpose eq301233 eq10
    | exact resolve eq10 eq301233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301233
  have eq301503 : y = (k y x) := by
    first
    | (have i₁ := eq301263
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq301263
    | exact resolve eq301263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301263
  have eq301615 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18794 y x
       have i₂ := eq301503
       grind)
    | exact superpose eq301503 eq18794
    | (have j0 := eq18794 x y
       grind)
    | (have r₁ := eq18794 y x
       have r₂ := eq301503
       grind)
    | exact resolve eq18794 eq301503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18794 eq301503
  have eq301627 : y = (M.op x y) ∨ x = y := by grind
  clear eq301615
  have eq301643 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq300589
       have i₂ := eq301627
       grind)
    | exact superpose eq301627 eq300589
    | exact resolve eq300589 eq301627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300589 eq301627
  have eq301710 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq301643
  have eq301734 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301710
       grind)
    | exact superpose eq301710 eq16
    | exact resolve eq16 eq301710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301710
  have eq301823 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq301734
       have r₂ := eq13934 x
       grind)
    | exact resolve eq301734 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301734
  have eq301828 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301823
       grind)
    | exact superpose eq301823 eq16
    | exact resolve eq16 eq301823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301836 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq301823
       grind)
    | exact superpose eq301823 eq10
    | exact resolve eq10 eq301823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301823
  have eq302100 : x = y := by
    first
    | (have i₁ := eq301836
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq301836
    | exact resolve eq301836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301836
  have eq302103 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq301828
       have i₂ := eq13934 x
       grind)
    | exact superpose eq13934 eq301828
    | exact resolve eq301828 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13934 eq301828
  have eq302167 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq302103
       have i₂ := eq302100
       grind)
    | exact superpose eq302100 eq302103
    | exact resolve eq302103 eq302100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302100 eq302103
  have eq302168 : False := by grind
  exact eq302168

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyy_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  clear eq22
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq100 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq100 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq100 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq104 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq101 (τ X0)
       grind)
    | exact superpose eq101 eq18
    | exact resolve eq18 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq113 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq110
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq104
    | exact resolve eq104 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq113
    | exact resolve eq113 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq113
  have eq136 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq61
    | exact resolve eq61 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq10
    | exact resolve eq10 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       grind)
    | exact resolve eq13 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq186 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq119 (M.op X0 X0)
       grind)
    | exact superpose eq119 eq180
    | (have j0 := eq180 X0 X1
       grind)
    | exact resolve eq180 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq191 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq186 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq186
    | (have j0 := eq186 X0 X1
       grind)
    | exact resolve eq186 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq192 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq195 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq119 (M.op X0 X0)
       grind)
    | exact superpose eq119 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq196 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq195 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq374 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq378 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq382 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X1 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1
       have i₂ := eq150 X1
       grind)
    | exact superpose eq150 eq378
    | (have j0 := eq378 X0 X1
       grind)
    | exact resolve eq378 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq386 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq119 X1
       grind)
    | exact superpose eq119 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq580 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq386
    | (have j0 := eq386 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq1380 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq196
    | exact resolve eq196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1407 : ∀ X0 X1 : G, (k (σ (τ (M.op X0 X0))) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1380 X0 X1
       have i₂ := eq150 X0
       grind)
    | exact superpose eq150 eq1380
    | (have j0 := eq1380 X0 X1
       grind)
    | exact resolve eq1380 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq1380
  have eq1417 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1407 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1407
    | (have j0 := eq1407 X0 X1
       grind)
    | exact resolve eq1407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1432 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1417 (M.op x x) (M.op X0 x)
       have i₂ := eq61 X0 x x
       grind)
    | exact superpose eq61 eq1417
    | exact resolve eq1417 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq20958 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X1 X1)) ∨ (τ (M.op X1 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20959 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ (M.op X1 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq21078 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20959 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20959
    | (have j0 := eq20959 (σ X1) (σ X0)
       grind)
    | exact resolve eq20959 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20959
  have eq21165 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21078 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq21078
    | (have j0 := eq21078 X0 X1
       grind)
    | exact resolve eq21078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21078
  have eq21213 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21165 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq21165
    | (have j0 := eq21165 X0 X1
       grind)
    | exact resolve eq21165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21165
  have eq21248 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21213 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21213
    | (have j0 := eq21213 X0 X1
       grind)
    | exact resolve eq21213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21213
  have eq21281 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21248 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq21248
    | (have j0 := eq21248 X0 X1
       grind)
    | exact resolve eq21248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21248
  have eq21313 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21281 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq21281
    | (have j0 := eq21281 X0 X1
       grind)
    | exact resolve eq21281 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21281
  have eq21343 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21313 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq21313
    | (have j0 := eq21313 X0 X1
       grind)
    | exact resolve eq21313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21313
  have eq21357 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21343 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21343
    | (have j0 := eq21343 X0 X1
       grind)
    | exact resolve eq21343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21343
  have eq21368 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21357 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21357
    | (have j0 := eq21357 X0 X1
       grind)
    | exact resolve eq21357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21357
  have eq21412 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21368 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq21368
    | (have j0 := eq21368 (σ X0) (σ X1)
       grind)
    | exact resolve eq21368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21368
  have eq21466 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21412 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq21412
    | (have j0 := eq21412 X0 X1
       grind)
    | exact resolve eq21412 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21412
  have eq24057 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20958 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20958
    | (have j0 := eq20958 (σ X1) (σ X0)
       grind)
    | exact resolve eq20958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20958
  have eq24160 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X0 X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24057 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq24057
    | (have j0 := eq24057 X0 X1
       grind)
    | exact resolve eq24057 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24057
  have eq24230 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24160 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq24160
    | (have j0 := eq24160 X0 X1
       grind)
    | exact resolve eq24160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24160
  have eq24276 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24230 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq24230
    | (have j0 := eq24230 X0 X1
       grind)
    | exact resolve eq24230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24230
  have eq24315 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24276
    | (have j0 := eq24276 X0 X1
       grind)
    | exact resolve eq24276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24276
  have eq24348 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24315 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq24315
    | (have j0 := eq24315 X0 X1
       grind)
    | exact resolve eq24315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24315
  have eq24378 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24348 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq24348
    | (have j0 := eq24348 X0 X1
       grind)
    | exact resolve eq24348 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24348
  have eq24399 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24378 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq24378
    | (have j0 := eq24378 X0 X1
       grind)
    | exact resolve eq24378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24378
  have eq24418 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24399 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24399
    | (have j0 := eq24399 X0 X1
       grind)
    | exact resolve eq24399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24399
  have eq24432 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24418 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24418
    | (have j0 := eq24418 X0 X1
       grind)
    | exact resolve eq24418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24418
  have eq24473 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24432 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq24432
    | (have j0 := eq24432 (σ X0) (σ X1)
       grind)
    | exact resolve eq24432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24432
  have eq24537 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24473 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq24473
    | (have j0 := eq24473 X0 X1
       grind)
    | exact resolve eq24473 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24473
  have eq24577 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24537 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq24537
    | (have j0 := eq24537 X0 X1
       grind)
    | exact resolve eq24537 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24537
  have eq27899 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X1 (σ X0)
       have i₂ := eq580 X0 X1
       grind)
    | exact superpose eq580 eq138
    | (have j0 := eq138 X0 (σ X1)
       have j1 := eq580 X1 X0
       grind)
    | (have r₁ := eq138 X1 (σ X0)
       have r₂ := eq580 X0 X1
       grind)
    | (have r₁ := eq138 X1 (σ X1)
       have r₂ := eq580 X1 X1
       grind)
    | (have r₁ := eq138 X1 (σ (M.op X1 X1))
       have r₂ := eq580 (M.op X1 X1) X1
       grind)
    | exact resolve eq138 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27937 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27938 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq27939 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27899 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27899
  have eq27974 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27939 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq27939
    | (have j0 := eq27939 X0 X1
       grind)
    | exact resolve eq27939 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27939
  have eq28047 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27938 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27938
  have eq28073 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq14 eq27974
    | (have j0 := eq27974 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq27974 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27974
  have eq28139 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28073 X1 X0
       have j1 := eq28047 X1 X0
       have j2 := eq27937 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27937 eq28047 eq28073
  have eq37019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28139 x y
       grind)
    | exact superpose eq28139 eq16
    | (have j1 := eq28139 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq28139 x y
       grind)
    | exact resolve eq16 eq28139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28139
  have eq37082 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37019
  have eq37214 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq37082
       grind)
    | exact superpose eq37082 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq37082
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq37082
       grind)
    | exact resolve eq12 eq37082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37225 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37214
  have eq37231 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37225
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37225
    | exact resolve eq37225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37225
  have eq37237 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37231
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq37231
    | exact resolve eq37231 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37231
  have eq37239 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq37237
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq37237 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37237
  have eq37241 : (M.op x y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq37239
       grind)
    | exact superpose eq37239 eq10
    | exact resolve eq10 eq37239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37239
  have eq37436 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37241
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq37241
    | exact resolve eq37241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37241
  have eq37550 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq37436
       grind)
    | exact superpose eq37436 eq61
    | exact resolve eq61 eq37436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37569 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1432 x y
       have i₂ := eq37550 x
       grind)
    | exact superpose eq37550 eq1432
    | (have j0 := eq1432 x y
       grind)
    | exact resolve eq1432 eq37550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432 eq37550
  have eq37694 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq37569
  have eq37712 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24577 y x
       have i₂ := eq37694
       grind)
    | exact superpose eq37694 eq24577
    | (have j0 := eq24577 y x
       grind)
    | exact resolve eq24577 eq37694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24577
  have eq37716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37082 eq37712
    | exact resolve eq37712 eq37082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37712
  have eq37717 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq37716
  have eq37725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37082 eq37717
    | exact resolve eq37717 eq37082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37717
  have eq37730 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq37725
       have r₂ := eq16
       grind)
    | exact resolve eq37725 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37725
  have eq37732 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37730 eq37082
    | exact resolve eq37082 eq37730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37082 eq37730
  have eq37772 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37732
       grind)
    | exact superpose eq37732 eq16
    | exact resolve eq16 eq37732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37778 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq37732
       grind)
    | exact superpose eq37732 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq37732
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq37732
       grind)
    | exact resolve eq12 eq37732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37779 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq37732
       grind)
    | exact superpose eq37732 eq61
    | exact resolve eq61 eq37732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37732
  have eq37789 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq37778
  have eq37795 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37789
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37789
    | exact resolve eq37789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37789
  have eq37801 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37795
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq37795
    | exact resolve eq37795 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37795
  have eq37810 : (k y x) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq37801
       grind)
    | exact superpose eq37801 eq10
    | exact resolve eq10 eq37801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37801
  have eq38006 : (k y x) = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37810
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq37810
    | exact resolve eq37810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37810
  have eq38010 : (k y x) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq38006
       have r₂ := eq12 y x
       grind)
    | exact resolve eq38006 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38006
  have eq38013 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq37694
       have i₂ := eq38010
       grind)
    | exact superpose eq38010 eq37694
    | exact resolve eq37694 eq38010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37694 eq38010
  have eq38022 : (M.op y y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq38013
  have eq38024 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38022 eq37772
    | exact resolve eq37772 eq38022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37772
  have eq38025 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38022 eq37436
    | exact resolve eq37436 eq38022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37436 eq38022
  have eq38152 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq38025
  have eq38170 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq38152
       grind)
    | exact superpose eq38152 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq38152
       grind)
    | exact resolve eq12 eq38152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38172 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq38152
       grind)
    | exact superpose eq38152 eq61
    | exact resolve eq61 eq38152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38152
  have eq38184 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq38170
       have r₂ := eq12 y x
       grind)
    | exact resolve eq38170 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38170
  have eq38422 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37779 (M.op x (σ x))
       have i₂ := eq37779 x
       grind)
    | exact superpose eq37779 eq37779
    | exact resolve eq37779 eq37779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37779
  have eq38443 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq38422
  have eq38450 : (σ x) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38443
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq38443
    | exact resolve eq38443 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38443
  have eq38454 : (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38450
       have r₂ := eq38024
       grind)
    | exact resolve eq38450 eq38024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38024 eq38450
  have eq38457 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38172 y
       have i₂ := eq38454
       grind)
    | exact superpose eq38454 eq38172
    | exact resolve eq38172 eq38454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38172 eq38454
  have eq38582 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq38457
  have eq38591 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38582
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq38582
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq38582
    | exact resolve eq38582 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38582
  have eq38596 : x = (M.op x y) ∨ x = y := by grind
  clear eq38591
  have eq38603 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 X0 x y
       have i₂ := eq38596
       grind)
    | exact superpose eq38596 eq61
    | exact resolve eq61 eq38596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq38615 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq38603 (M.op x x)
       have i₂ := eq38603 x
       grind)
    | exact superpose eq38603 eq38603
    | exact resolve eq38603 eq38603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38603
  have eq38630 : x = (M.op x x) ∨ x = y := by grind
  clear eq38615
  have eq38632 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq38184
       have i₂ := eq38630
       grind)
    | exact superpose eq38630 eq38184
    | (have r₁ := eq38184
       have r₂ := eq38630
       grind)
    | exact resolve eq38184 eq38630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38184 eq38630
  have eq38769 : x = (k y x) ∨ x = y := by grind
  clear eq38632
  have eq38784 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq21466 y x
       have i₂ := eq38769
       grind)
    | exact superpose eq38769 eq21466
    | (have j0 := eq21466 y x
       grind)
    | exact resolve eq21466 eq38769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21466
  have eq38791 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq38784
  have eq44160 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq38791
       grind)
    | exact superpose eq38791 eq16
    | exact resolve eq16 eq38791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44169 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq138 y (σ x)
       have i₂ := eq38791
       grind)
    | exact superpose eq38791 eq138
    | (have j0 := eq138 y (σ x)
       grind)
    | (have r₁ := eq138 y (σ x)
       have r₂ := eq38791
       grind)
    | exact resolve eq138 eq38791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq38791
  have eq44185 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq44169
  have eq44198 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44185
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq44185
    | exact resolve eq44185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44185
  have eq44203 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq38596 eq44160
    | exact resolve eq44160 eq38596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44160
  have eq44212 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq38769 eq44198
    | exact resolve eq44198 eq38769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38769 eq44198
  have eq44213 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq44212
  have eq44221 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq44213
       have r₂ := eq44203
       grind)
    | exact resolve eq44213 eq44203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44203 eq44213
  have eq44236 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq44221
       grind)
    | exact superpose eq44221 eq16
    | exact resolve eq16 eq44221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44221
  have eq44272 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq38596 eq44236
    | exact resolve eq44236 eq38596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38596 eq44236
  have eq44273 : x = y := by grind
  clear eq44272
  have eq44288 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44273
       grind)
    | exact superpose eq44273 eq16
    | exact resolve eq16 eq44273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44273
  have eq44292 : False := by grind
  exact eq44292

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyy_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
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
  have eq176 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq176 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x y X0
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) (σ y) X0
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 X0 x y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 X0 (σ x) (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq184 eq176
    | exact resolve eq176 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq185 eq176
    | exact resolve eq176 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq188 eq176
    | exact resolve eq176 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq886 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq886 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq886 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq906 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq196 sF0
       have i₂ := eq887 sF0
       grind)
    | exact superpose eq887 eq196
    | exact resolve eq196 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq908 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq201 sF4
       have i₂ := eq887 sF4
       grind)
    | exact superpose eq887 eq201
    | exact resolve eq201 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq910 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 X0
       have i₂ := eq887 (M.op X0 X0)
       grind)
    | exact superpose eq887 eq176
    | exact resolve eq176 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq917 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq910 X0
       have i₂ := eq887 X0
       grind)
    | exact superpose eq887 eq910
    | exact resolve eq910 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1005 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (k y (k (M.op x y) (M.op x y))) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq906 eq13
    | (have j0 := eq13 y (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1016 : (k y (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) ≠ (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq887 (k sF0 sF0)
       grind)
    | exact superpose eq887 eq1005
    | exact resolve eq1005 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1020 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1016
       have i₂ := eq917 sF0
       grind)
    | exact superpose eq917 eq1016
    | exact resolve eq1016 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1742 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq773
       grind)
    | exact superpose eq773 eq39
    | exact resolve eq39 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq1743 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1742
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1742
    | exact resolve eq1742 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq1745 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1743
    | exact resolve eq1743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1745 eq776
    | exact resolve eq776 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1946
       have r₂ := eq27
       grind)
    | exact resolve eq1946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946
  have eq1958 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1953 eq185
    | exact resolve eq185 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1959 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1953 eq189
    | exact resolve eq189 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1962 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1953 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1953
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1953
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1953
       grind)
    | exact resolve eq12 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1980 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1962
       have r₂ := eq26
       grind)
    | exact resolve eq1962 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq1982 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1959
       have i₂ := eq887 sF4
       grind)
    | exact superpose eq887 eq1959
    | exact resolve eq1959 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq1983 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1958
       have i₂ := eq887 sF4
       grind)
    | exact superpose eq887 eq1958
    | exact resolve eq1958 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq1985 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1980
    | exact resolve eq1980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq1986 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1985
  have eq1988 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1982 eq1983
    | exact resolve eq1983 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq1989 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1986
       have i₂ := eq887 sF3
       grind)
    | exact superpose eq887 eq1986
    | exact resolve eq1986 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq1990 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1745 eq1989
    | exact resolve eq1989 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq1991 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1988 eq1990
    | exact resolve eq1990 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988 eq1990
  have eq2169 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1982 eq917
    | exact resolve eq917 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq2176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1991 eq2169
    | exact resolve eq2169 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991 eq2169
  have eq2178 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2176
       have r₂ := eq27
       grind)
    | exact resolve eq2176 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2181 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184 x
       have i₂ := eq2178
       grind)
    | exact superpose eq2178 eq184
    | exact resolve eq184 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2182 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq2178
       grind)
    | exact superpose eq2178 eq188
    | exact resolve eq188 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq2205 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2182
       have i₂ := eq887 sF0
       grind)
    | exact superpose eq887 eq2182
    | exact resolve eq2182 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182
  have eq2206 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2181
       have i₂ := eq887 sF0
       grind)
    | exact superpose eq887 eq2181
    | exact resolve eq2181 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq2211 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2205 eq2206
    | exact resolve eq2206 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205 eq2206
  have eq2213 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2211 eq27
    | exact resolve eq27 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2217 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2211 eq189
    | exact resolve eq189 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2211 eq908
    | exact resolve eq908 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq2211
  have eq2869 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2217 eq2217
    | exact resolve eq2217 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2902 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2869
  have eq2908 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2902
       have i₂ := eq887 sF2
       grind)
    | exact superpose eq887 eq2902
    | exact resolve eq2902 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq3228 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (k (σ y) (k (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2224 eq13
    | (have j0 := eq13 (σ y) (k (σ x) (σ x))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2224
       grind)
    | exact resolve eq13 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq3253 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (k (σ y) (k (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3228
       have r₂ := eq2908
       grind)
    | exact resolve eq3228 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3259 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (k (σ y) (k (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3253
       have i₂ := eq887 (k sF2 sF2)
       grind)
    | exact superpose eq887 eq3253
    | exact resolve eq3253 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq3264 : (σ x) = (k (σ y) (k (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3259
       have i₂ := eq917 sF2
       grind)
    | exact superpose eq917 eq3259
    | exact resolve eq3259 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq3259
  have eq3268 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2908 eq3264
    | exact resolve eq3264 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908 eq3264
  have eq3274 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3268 eq1745
    | exact resolve eq1745 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745 eq3268
  have eq3282 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3274
  have eq3289 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3282
       have r₂ := eq2213
       grind)
    | exact resolve eq3282 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213 eq3282
  have eq3306 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq184 x
       have i₂ := eq3289
       grind)
    | exact superpose eq3289 eq184
    | exact resolve eq184 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq3307 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq3289
       grind)
    | exact superpose eq3289 eq188
    | exact resolve eq188 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq3289
  have eq3334 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3307
       have i₂ := eq887 sF0
       grind)
    | exact superpose eq887 eq3307
    | exact resolve eq3307 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq3335 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3306
       have i₂ := eq887 sF0
       grind)
    | exact superpose eq887 eq3306
    | exact resolve eq3306 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3306
  have eq3340 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3334 eq3335
    | exact resolve eq3335 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq3335
  have eq3341 : x = (M.op x y) ∨ x = y := by grind
  clear eq3340
  have eq3344 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq3341
       grind)
    | exact superpose eq3341 eq18
    | exact resolve eq18 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3345 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq3341
       grind)
    | exact superpose eq3341 eq22
    | exact resolve eq22 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3363 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq3345
    | exact resolve eq3345 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3398 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3344 eq208
    | exact resolve eq208 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq3344
  have eq3421 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3341 eq3398
    | exact resolve eq3398 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq3398
  have eq3423 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq3421
       have i₂ := eq887 sF0
       grind)
    | exact superpose eq887 eq3421
    | exact resolve eq3421 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3428 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3423 eq1020
    | (have r₁ := eq1020
       have r₂ := eq3423
       grind)
    | exact resolve eq1020 eq3423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq3423
  have eq3445 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by grind
  clear eq3428
  have eq3458 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3445 eq36
    | exact resolve eq36 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3445
  have eq3463 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq3458
    | exact resolve eq3458 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq3465 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq3363 eq3463
    | exact resolve eq3463 eq3363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463
  have eq3503 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3465 eq776
    | exact resolve eq776 eq3465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq3465
  have eq3509 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq3503
  have eq4193 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3509 eq185
    | exact resolve eq185 eq3509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq4197 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3509 eq189
    | exact resolve eq189 eq3509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq3509
  have eq4231 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4197
       have i₂ := eq887 sF4
       grind)
    | exact superpose eq887 eq4197
    | exact resolve eq4197 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4197
  have eq4232 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4193
       have i₂ := eq887 sF4
       grind)
    | exact superpose eq887 eq4193
    | exact resolve eq4193 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4238 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4231 eq4232
    | exact resolve eq4232 eq4231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4231 eq4232
  have eq4245 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4238 eq27
    | exact resolve eq27 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4280 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq4245
       have r₂ := eq3363
       grind)
    | exact resolve eq4245 eq3363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363 eq4245
  have eq4288 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4280 eq31
    | exact resolve eq31 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4280
  have eq4331 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq4288
    | exact resolve eq4288 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4288
  have eq4332 : x = y := by grind
  clear eq4331
  have eq4347 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4332
       grind)
    | exact superpose eq4332 eq18
    | exact resolve eq18 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4348 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4332
       grind)
    | exact superpose eq4332 eq24
    | exact resolve eq24 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4332
  have eq4372 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4348
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4348
    | exact resolve eq4348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4348
  have eq4373 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq4347
       have i₂ := eq887 x
       grind)
    | exact superpose eq887 eq4347
    | exact resolve eq4347 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347
  have eq4374 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4372 eq26
    | exact resolve eq26 eq4372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4372
  have eq4412 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4374
       have i₂ := eq887 sF2
       grind)
    | exact superpose eq887 eq4374
    | exact resolve eq4374 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq4374
  have eq4421 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq4373
       grind)
    | exact superpose eq4373 eq39
    | exact resolve eq39 eq4373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4373
  have eq4435 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4421
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4421
    | exact resolve eq4421 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4421
  have eq4441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4412 eq4435
    | exact resolve eq4435 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412 eq4435
  have eq4443 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4441
    | exact resolve eq4441 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4441
  have eq4445 : False := by grind
  exact eq4445

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq100 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq100 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq100 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq104 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq101 (τ X0)
       grind)
    | exact superpose eq101 eq18
    | exact resolve eq18 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq108
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq104
    | exact resolve eq104 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq111
    | exact resolve eq111 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq123 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq115
    | exact resolve eq115 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq61
    | exact resolve eq61 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq61
    | exact resolve eq61 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq10
    | exact resolve eq10 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (τ X0) (τ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq61
    | exact resolve eq61 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1 (τ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq67
    | exact resolve eq67 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq150 (σ X1) (σ X0)
       grind)
    | exact superpose eq150 eq15
    | (have j1 := eq150 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq150 X1 (σ X0)
       grind)
    | exact superpose eq150 eq22
    | (have j1 := eq150 X1 (σ X0)
       grind)
    | exact resolve eq22 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq293 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq295 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq431 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq295 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq295
    | exact resolve eq295 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq2394 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq293 (M.op X0 X0) (M.op (σ X0) X1)
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq293
    | (have j0 := eq293 (M.op X0 X0) (M.op (σ X0) X1)
       grind)
    | exact resolve eq293 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq293
  have eq2446 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2394 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2394
    | (have j0 := eq2394 X0 X1
       grind)
    | exact resolve eq2394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2454 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) ∨ (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2446 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq2446 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq2446
    | (have j0 := eq2446 X0 X1
       grind)
    | exact resolve eq2446 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq7661 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq431 X0 X1 X2
       have i₂ := eq123 X0 X1
       grind)
    | exact superpose eq123 eq431
    | (have j0 := eq431 X0 X1 X2
       grind)
    | exact resolve eq431 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq431
  have eq8139 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) ≠ (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq7661 X0 X1 X2
       grind)
    | exact superpose eq7661 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq7661 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq7661 X0 X1 X2
       grind)
    | exact resolve eq13 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7661
  have eq8154 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8139 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8139
  have eq8159 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (σ (M.op X2 X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8154 X0 X1 X2
       have i₂ := eq115 X2
       grind)
    | exact superpose eq115 eq8154
    | (have j0 := eq8154 X0 X1 X2
       grind)
    | exact resolve eq8154 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8154
  have eq8193 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8159 X0 X1 X2
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq8159
    | (have j0 := eq8159 X0 X1 X2
       grind)
    | exact resolve eq8159 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8159
  have eq29092 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) X1 (σ (M.op X0 X0))
       have i₂ := eq2454 X0 X1
       grind)
    | exact superpose eq2454 eq62
    | (have j1 := eq2454 X0 X1
       grind)
    | exact resolve eq62 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29115 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X2)) ∨ (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op (σ X0) X1) (σ (M.op X0 X0)) x
       have i₂ := eq2454 X0 X1
       grind)
    | exact superpose eq2454 eq62
    | (have j1 := eq2454 X0 X1
       grind)
    | exact resolve eq62 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq29164 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29092 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq29092
    | (have j0 := eq29092 X0 X1
       grind)
    | exact resolve eq29092 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29092
  have eq29278 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (M.op (τ X0) (τ X0))) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29164 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29164
    | exact resolve eq29164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29164
  have eq29485 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29278 X0 X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq29278
    | (have j0 := eq29278 X0 X1
       grind)
    | exact resolve eq29278 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29278
  have eq29510 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29485 X0 X1
       have i₂ := eq31 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact superpose eq31 eq29485
    | (have j0 := eq29485 X0 X1
       grind)
    | exact resolve eq29485 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29485
  have eq29523 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29510 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq29510
    | (have j0 := eq29510 X0 X1
       grind)
    | exact resolve eq29510 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29510
  have eq29651 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X0 X1) (M.op X0 X0))
       have i₂ := eq29523 X0 X1
       grind)
    | exact superpose eq29523 eq11
    | (have j1 := eq29523 X0 X1
       grind)
    | exact resolve eq11 eq29523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523
  have eq29806 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29651 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29651
    | (have j0 := eq29651 X0 X1
       grind)
    | exact resolve eq29651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29651
  have eq30007 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f30007_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = X1 := by
      intro X0 X1 X2
      grind
    have f30007_18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f30007_20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
      intro X0 X1
      grind
    have f30007_23 : (M.op X1 X0) ≠ (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by grind
    have f30007_24 : X0 ≠ (M.op (M.op X1 X0) (M.op X1 X0)) := by grind
    have f30007_26 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
      intro X0 X1 X2
      first
      | (have i₁ := f30007_14 X1 (M.op X2 X0) (M.op X0 x)
         have i₂ := f30007_14 X2 X0 x
         grind)
      | exact superpose f30007_14 f30007_14
      | exact resolve f30007_14 f30007_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_148 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
      intro X0 X1
      first
      | (have i₁ := f30007_14 X1 X1 X1
         have i₂ := f30007_20 X0 (M.op X1 X1)
         grind)
      | (have i₁ := f30007_14 X0 X1 x
         have i₂ := f30007_20 (M.op X0 X1) (M.op X1 x)
         grind)
      | exact superpose f30007_20 f30007_14
      | (have j1 := f30007_20 X0 (M.op X1 X1)
         grind)
      | exact resolve f30007_14 f30007_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_159 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = X1 := by
      intro X0 X1
      first
      | (have j0 := f30007_148 X0 X1
         have j1 := f30007_18 X0 (M.op X1 X1)
         grind)
      | (have r₁ := f30007_148 X1 X1
         have r₂ := f30007_18 (M.op X1 X1) X1
         grind)
      | (have r₁ := f30007_148 X0 X1
         have r₂ := f30007_18 X0 (M.op X1 X1)
         grind)
      | exact resolve f30007_148 f30007_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_947 : (M.op X1 X0) ≠ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X0) ∨ (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
      first
      | (have i₁ := f30007_23
         have i₂ := f30007_159 X0 (M.op X1 X0)
         grind)
      | exact superpose f30007_159 f30007_23
      | (have j1 := f30007_159 X0 (M.op X1 X0)
         grind)
      | exact resolve f30007_23 f30007_159
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_948 : (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
      first
      | (have r₁ := f30007_947
         have r₂ := f30007_26 X0 (M.op X1 X0) X1
         grind)
      | exact resolve f30007_947 f30007_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_1884 : ∀ X0 : G, X0 = (M.op (M.op X0 X0) (M.op X1 X0)) := by
      intro X0
      first
      | (have i₁ := f30007_14 X0 X0 (M.op (M.op X1 X0) (M.op X1 X0))
         have i₂ := f30007_948
         grind)
      | exact superpose f30007_948 f30007_14
      | exact resolve f30007_14 f30007_948
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_1959 : X0 ≠ X0 := by
      first
      | (have i₁ := f30007_24
         have i₂ := f30007_1884 X1
         grind)
      | exact superpose f30007_1884 f30007_24
      | (have r₁ := f30007_24
         have r₂ := f30007_1884 X1
         grind)
      | exact resolve f30007_24 f30007_1884
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f30007_2011 : False := by grind
    exact f30007_2011
  clear eq29806
  have eq47868 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op (M.op X2 (τ (σ X0))) (τ (M.op (σ X0) X1))) ∨ (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162 (M.op (σ X0) X2) X1
       have i₂ := eq29115 X0 X2 X2
       grind)
    | exact superpose eq29115 eq162
    | (have j1 := eq29115 X0 X1 X2
       grind)
    | exact resolve eq162 eq29115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq29115
  have eq48051 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 ∨ (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47868 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47868
    | (have j0 := eq47868 X0 X1 X2
       grind)
    | exact resolve eq47868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47868
  have eq48776 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 X1)) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (M.op X2 (τ X0)) (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48051 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48051
    | exact resolve eq48051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48856 : ∀ X0 X1 X2 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) ∨ (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 (M.op (σ X0) X1) (M.op X0 X0)
       have i₂ := eq48051 X0 X1 X2
       grind)
    | exact superpose eq48051 eq17
    | (have j1 := eq48051 X0 X1 X2
       grind)
    | exact resolve eq17 eq48051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48051
  have eq49004 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (M.op X2 (τ X0)) (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48776 X0 X1 X2
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq48776
    | (have j0 := eq48776 X0 X1 X2
       grind)
    | exact resolve eq48776 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48776
  have eq49043 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X2 (τ X0)) (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49004 X0 X1 X2
       have i₂ := eq31 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact superpose eq31 eq49004
    | (have j0 := eq49004 X0 X1 X2
       grind)
    | exact resolve eq49004 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49004
  have eq56085 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op X2 (τ X0)) (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48856 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48856
    | exact resolve eq48856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48856
  have eq56314 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X2 (τ X0)) (τ (M.op X0 X1))) ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56085 X0 X1 X2
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq56085
    | (have j0 := eq56085 X0 X1 X2
       grind)
    | exact resolve eq56085 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56085
  have eq56598 : ∀ X0 X2 X3 : G, (τ (M.op X0 X2)) = (M.op (τ X0) (M.op (τ (M.op X0 X2)) X3)) ∨ (k (M.op X0 X2) (M.op X0 X0)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 (τ (M.op X0 X2)) x (τ X0) X3
       have i₂ := eq56314 X0 X2 x
       grind)
    | exact superpose eq56314 eq9
    | (have j1 := eq56314 X0 X2 X2
       grind)
    | exact resolve eq9 eq56314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56314
  have eq59317 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49043 X0 X1 (τ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq49043
    | (have j0 := eq49043 X0 X1 x
       grind)
    | exact resolve eq49043 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59514 : ∀ X0 X2 : G, (τ X0) = (k (τ (M.op X0 X2)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X2)) ∨ (τ X0) = (τ (k (M.op X0 X2) (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq30007 (τ (M.op X0 x)) (M.op X2 (τ X0))
       have i₂ := eq49043 X0 x X2
       grind)
    | exact superpose eq49043 eq30007
    | (have j1 := eq49043 X0 X2 X2
       grind)
    | exact resolve eq30007 eq49043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30007 eq49043
  have eq59538 : ∀ X0 X2 : G, (τ X0) = (k (τ (M.op X0 X2)) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X2)) ∨ (τ X0) = (τ (k (M.op X0 X2) (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq59514 X0 X2
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq59514
    | (have j0 := eq59514 X0 X2
       grind)
    | exact resolve eq59514 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59514
  have eq59641 : ∀ X0 X2 : G, (τ X0) = (τ (k (M.op X0 X2) (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X2)) ∨ (τ X0) = (τ (k (M.op X0 X2) (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq59538 X0 X2
       have i₂ := eq31 (M.op X0 X0) (M.op X0 X2)
       grind)
    | exact superpose eq31 eq59538
    | (have j0 := eq59538 X0 X2
       grind)
    | exact resolve eq59538 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59538
  have eq59642 : ∀ X0 X2 : G, (τ X0) = (τ (k (M.op X0 X2) (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have j0 := eq59641 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59641
  have eq59713 : ∀ X0 X2 : G, (τ X0) = (τ (k (M.op X0 X2) (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq59642 X0 X2
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq59642
    | (have j0 := eq59642 X0 X2
       grind)
    | exact resolve eq59642 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59642
  have eq59932 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X0 X1) (M.op X0 X0))
       have i₂ := eq59713 X0 X1
       grind)
    | exact superpose eq59713 eq11
    | (have j1 := eq59713 X0 X1
       grind)
    | exact resolve eq11 eq59713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59713
  have eq60114 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (τ (M.op X0 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59932 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59932
    | (have j0 := eq59932 X0 X1
       grind)
    | exact resolve eq59932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59932
  have eq60538 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) ∨ (τ (τ (M.op X0 X0))) = (τ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60114 (τ X0) X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq60114
    | exact resolve eq60114 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60114
  have eq82621 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) ∨ (τ (τ (M.op X0 X0))) = (τ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X0) (M.op (τ X0) X1)
       have i₂ := eq60538 X0 X1
       grind)
    | exact superpose eq60538 eq18
    | (have j1 := eq60538 X0 X1
       grind)
    | exact resolve eq18 eq60538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq60538
  have eq82738 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) = X0 ∨ (τ (τ (M.op X0 X0))) = (τ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82621 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82621
    | (have j0 := eq82621 X0 X1
       grind)
    | exact resolve eq82621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82621
  have eq82965 : ∀ X0 X1 : G, (k (σ (τ (M.op X0 X1))) (M.op X0 X0)) = X0 ∨ (τ (τ (M.op X0 X0))) = (τ (τ (M.op X0 X1))) ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82738 X0 (M.op (τ (M.op X0 x)) x)
       have i₂ := eq56598 X0 x x
       grind)
    | exact superpose eq56598 eq82738
    | (have j1 := eq56598 X0 X1 x
       grind)
    | exact resolve eq82738 eq56598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56598 eq82738
  have eq83162 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (τ (τ (M.op X0 X0))) = (τ (τ (M.op X0 X1))) ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82965 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq82965
    | (have j0 := eq82965 X0 X1
       grind)
    | exact resolve eq82965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82965
  have eq83163 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (τ (τ (M.op X0 X1))) ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq83162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83162
  have eq83275 : ∀ X0 X1 : G, (τ (τ (σ (M.op X0 X0)))) = (τ (τ (M.op (σ X0) X1))) ∨ (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83163 (σ X0) X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq83163
    | exact resolve eq83163 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83163
  have eq84041 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq83275 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq83275
    | (have j0 := eq83275 X0 X1
       grind)
    | exact resolve eq83275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83275
  have eq119622 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) (M.op X0 X0)
       have i₂ := eq84041 X0 X1
       grind)
    | exact superpose eq84041 eq22
    | (have j1 := eq84041 X0 X1
       grind)
    | exact resolve eq22 eq84041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84041
  have eq119721 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 ∨ (τ (M.op X0 X0)) = (τ (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119622 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq119622
    | (have j0 := eq119622 X0 X1
       grind)
    | exact resolve eq119622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119622
  have eq120107 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (σ (τ X0)) X1)) (τ (M.op X0 X0))) ∨ (τ (τ (M.op X0 X0))) = (τ (τ (M.op (σ (τ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119721 (τ X0) X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq119721
    | exact resolve eq119721 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119721
  have eq120266 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op (σ (τ X0)) X1) (M.op X0 X0))) ∨ (τ (τ (M.op X0 X0))) = (τ (τ (M.op (σ (τ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq120107 X0 X1
       have i₂ := eq31 (M.op X0 X0) (M.op (σ (τ X0)) X1)
       grind)
    | exact superpose eq31 eq120107
    | (have j0 := eq120107 X0 X1
       grind)
    | exact resolve eq120107 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120107
  have eq120349 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (τ (τ (M.op X0 X0))) = (τ (τ (M.op (σ (τ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq120266 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120266
    | (have j0 := eq120266 X0 X1
       grind)
    | exact resolve eq120266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120266
  have eq120416 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (τ (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq120349 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120349
    | (have j0 := eq120349 X0 X1
       grind)
    | exact resolve eq120349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120349
  have eq120845 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (σ (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0))))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (τ (M.op X0 X0))
       have i₂ := eq120416 X0 X1
       grind)
    | (have i₁ := eq119 (τ (M.op X0 X1))
       have i₂ := eq120416 X0 X1
       grind)
    | exact superpose eq120416 eq119
    | (have j1 := eq120416 X0 X1
       grind)
    | exact resolve eq119 eq120416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120416
  have eq121121 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq120845 X0 X1
       have i₂ := eq119 (τ (M.op X0 X0))
       grind)
    | exact superpose eq119 eq120845
    | (have j0 := eq120845 X0 X1
       grind)
    | exact resolve eq120845 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120845
  have eq121387 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq121121 X0 X1
       have i₂ := eq145 (M.op X0 X1)
       grind)
    | exact superpose eq145 eq121121
    | (have j0 := eq121121 X0 X1
       grind)
    | exact resolve eq121121 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121121
  have eq121552 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (τ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq121387 X0 X1
       have i₂ := eq145 (M.op X0 X0)
       grind)
    | exact superpose eq145 eq121387
    | (have j0 := eq121387 X0 X1
       grind)
    | exact resolve eq121387 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121387
  have eq121632 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (τ X0) = (τ (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121552 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq121552 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq121552
    | (have j0 := eq121552 X0 X1
       grind)
    | exact resolve eq121552 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121552
  have eq328820 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ (τ X0))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (k (τ X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8193 X0 X1 (τ X0)
       have i₂ := eq17 X0 (k (τ X0) X1)
       grind)
    | exact superpose eq17 eq8193
    | (have j0 := eq8193 X1 X2 (τ X0)
       grind)
    | exact resolve eq8193 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8193
  have eq329233 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (k (τ X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq328820 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq328820
    | (have j0 := eq328820 X0 X1 X2
       grind)
    | exact resolve eq328820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328820
  have eq329375 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (k (τ X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq329233 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq329233
    | (have j0 := eq329233 X0 X1 X2
       grind)
    | exact resolve eq329233 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329233
  have eq329488 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (k (τ X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq329375 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq329375
    | (have j0 := eq329375 X0 X1 X2
       grind)
    | exact resolve eq329375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329375
  have eq329575 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (k (τ X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq329488 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq329488 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq329488 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329488
  have eq329648 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq329575 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq329575
    | (have j0 := eq329575 X0 X1 X2
       grind)
    | exact resolve eq329575 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq329575
  have eq329702 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = (k X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq329648 X0 X1 X2
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq329648
    | (have j0 := eq329648 X0 X1 X2
       grind)
    | exact resolve eq329648 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329648
  have eq1042128 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op (k X2 X0) X1) ∨ (M.op X1 X1) = (k X1 (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq329702 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq329702
    | exact resolve eq329702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329702
  have eq1045426 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (k X1 X2) X0) ∨ (M.op X0 X0) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1042128 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045979 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1045426 X0 X0 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq1045426
    | exact resolve eq1045426 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq1045426
  have eq1050983 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1045979 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq1045979
    | exact resolve eq1045979 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045979
  have eq1052235 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1050983 (M.op X1 (τ X0)) (τ (M.op X0 X0))
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq1050983
    | (have j0 := eq1050983 (M.op X1 (τ X0)) (τ (M.op X0 X0))
       grind)
    | exact resolve eq1050983 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1050983
  have eq1052653 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1052235 X0 X1
       have i₂ := eq145 (M.op X0 X0)
       grind)
    | exact superpose eq145 eq1052235
    | (have j0 := eq1052235 X0 X1
       grind)
    | exact resolve eq1052235 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052235
  have eq1052895 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1052653 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq1052653 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq1052653
    | (have j0 := eq1052653 X0 X1
       grind)
    | exact resolve eq1052653 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052653
  have eq1052896 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1052895 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052895
  have eq1053107 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1052896 X0 X1
       have i₂ := eq145 (M.op X0 X0)
       grind)
    | exact superpose eq145 eq1052896
    | exact resolve eq1052896 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052896
  have eq1053248 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1053107 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq1053107 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq1053107
    | exact resolve eq1053107 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053107
  have eq1053595 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1053248 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1053248
    | exact resolve eq1053248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053248
  have eq1054291 : ∀ X0 X1 : G, (k (τ (σ (M.op X0 X0))) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1053595 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq1053595
    | exact resolve eq1053595 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053595
  have eq1054457 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1054291 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1054291
    | exact resolve eq1054291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054291
  have eq1055486 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1042128 (M.op X1 X0) X1 (M.op X0 X0)
       have i₂ := eq1054457 X0 X1
       grind)
    | exact superpose eq1054457 eq1042128
    | exact resolve eq1042128 eq1054457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042128 eq1054457
  have eq1076835 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1055486 X1 (σ X0)
       grind)
    | exact superpose eq1055486 eq28
    | (have j1 := eq1055486 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1055486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077797 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1055486 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055486
  have eq1078337 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076835 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq1076835
    | (have j0 := eq1076835 X0 X1
       grind)
    | exact resolve eq1076835 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076835
  have eq1079223 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1078337 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1078337
    | (have j0 := eq1078337 X0 X1
       grind)
    | exact resolve eq1078337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078337
  have eq1091988 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1077797 (τ (M.op X0 X1)) (τ (M.op X0 X0))
       have i₂ := eq59317 X0 X1
       grind)
    | exact superpose eq59317 eq1077797
    | (have j1 := eq59317 X0 X1
       grind)
    | exact resolve eq1077797 eq59317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59317 eq1077797
  have eq1092446 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1091988 X0 X1
       have i₂ := eq145 (M.op X0 X1)
       grind)
    | exact superpose eq145 eq1091988
    | (have j0 := eq1091988 X0 X1
       grind)
    | exact resolve eq1091988 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091988
  have eq1092675 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1092446 X0 X1
       have j1 := eq121632 X0 X1
       grind)
    | (have r₁ := eq1092446 X0 X1
       have r₂ := eq121632 X0 X1
       grind)
    | exact resolve eq1092446 eq121632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121632 eq1092446
  have eq1092794 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1092675 X0 X1
       have i₂ := eq31 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact superpose eq31 eq1092675
    | (have j0 := eq1092675 X0 X1
       grind)
    | exact resolve eq1092675 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092675
  have eq1092795 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1092794 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092794
  have eq1093220 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (τ (k (σ X0) (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1092795 (M.op X1 (σ X0)) (σ (M.op X0 X0))
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq1092795
    | exact resolve eq1092795 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093514 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (k (M.op (σ X0) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1092795 (σ X0) X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq1092795
    | exact resolve eq1092795 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1092795
  have eq1093984 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1093514 X0 X1
       have i₂ := eq22 (M.op (σ X0) X1) (M.op X0 X0)
       grind)
    | exact superpose eq22 eq1093514
    | exact resolve eq1093514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1093514
  have eq1094097 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1093220 X0 X1
       have i₂ := eq28 X0 (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0)))
       grind)
    | exact superpose eq28 eq1093220
    | exact resolve eq1093220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1093220
  have eq1094313 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1093984 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1093984
    | exact resolve eq1093984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093984
  have eq1249981 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1079223 X1 (σ X0)
       grind)
    | exact superpose eq1079223 eq15
    | (have j1 := eq1079223 X1 (σ X0)
       grind)
    | exact resolve eq15 eq1079223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079223
  have eq1250785 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1249981 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1249981
    | (have j0 := eq1249981 X0 X1
       grind)
    | exact resolve eq1249981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249981
  have eq1269511 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ (M.op X0 X0))) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 (σ X1)
       have i₂ := eq1250785 X1 X0
       grind)
    | exact superpose eq1250785 eq129
    | (have j1 := eq1250785 X1 X0
       grind)
    | exact resolve eq129 eq1250785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1250785
  have eq2342561 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (σ (M.op (τ X0) (τ X0)))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1269511 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1269511
    | exact resolve eq1269511 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1269511
  have eq2344188 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (M.op X0 X0)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2342561 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq2342561
    | (have j0 := eq2342561 X0 X1
       grind)
    | exact resolve eq2342561 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342561
  have eq2344772 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (k X0 X1) (M.op X0 X0)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2344188 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2344188
    | (have j0 := eq2344188 X0 X1
       grind)
    | exact resolve eq2344188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344188
  have eq2345179 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 X0)) = X0 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2344772 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2344772
    | (have j0 := eq2344772 X0 X1
       grind)
    | exact resolve eq2344772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344772
  have eq2345430 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X0)) ∨ (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2345179 X0 X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq2345179
    | (have j0 := eq2345179 X0 X1
       grind)
    | exact resolve eq2345179 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345179
  have eq2351821 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (k X0 X1)) (τ (k X0 X1)))) ∨ (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (M.op X0 X0)
       have i₂ := eq2345430 X0 X1
       grind)
    | exact superpose eq2345430 eq119
    | (have j1 := eq2345430 X0 X1
       grind)
    | exact resolve eq119 eq2345430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345430
  have eq2352413 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2351821 X0 X1
       have i₂ := eq119 (k X0 X1)
       grind)
    | exact superpose eq119 eq2351821
    | (have j0 := eq2351821 X0 X1
       grind)
    | exact resolve eq2351821 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq2351821
  have eq2353021 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = X0 ∨ (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2352413 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq2352413 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq2352413
    | (have j0 := eq2352413 X0 X1
       grind)
    | exact resolve eq2352413 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352413
  have eq2355798 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (k X0 X1) (k X0 X1) x
       have i₂ := eq2353021 X0 X1
       grind)
    | exact superpose eq2353021 eq62
    | (have j1 := eq2353021 X0 X1
       grind)
    | exact resolve eq62 eq2353021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2353021
  have eq2401356 : ∀ X0 X1 : G, (τ X0) = (M.op (k (τ X0) X1) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (k (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2355798 (τ X0) X1 (τ X0)
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq2355798
    | exact resolve eq2355798 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2401949 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2355798 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355798
  have eq2401950 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2401949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401949
  have eq2402002 : ∀ X0 X1 : G, (τ X0) = (M.op (k (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2401356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401356
  have eq2404516 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op (M.op X1 (k X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (k X0 X2) (M.op X0 X0)
       have i₂ := eq2401950 X0 X2
       grind)
    | exact superpose eq2401950 eq61
    | exact resolve eq61 eq2401950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401950
  have eq2417322 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2404516 (τ (M.op (σ X0) X1)) X1 (M.op X0 X0)
       have i₂ := eq1094313 X0 X1
       grind)
    | exact superpose eq1094313 eq2404516
    | exact resolve eq2404516 eq1094313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094313 eq2404516
  have eq2447085 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op X0 (σ (τ X1)))) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2402002 X1 (τ (M.op (M.op X0 (σ (τ X1))) (M.op X0 (σ (τ X1)))))
       have i₂ := eq1094097 (τ X1) X0
       grind)
    | exact superpose eq1094097 eq2402002
    | exact resolve eq2402002 eq1094097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094097 eq2402002
  have eq2447924 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op X0 X1)) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2447085 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2447085
    | exact resolve eq2447085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447085
  have eq2466111 : ∀ X0 X1 X2 : G, (τ (M.op X2 X0)) = (M.op (M.op X1 (τ (M.op X2 X0))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (τ (M.op X2 X0)) (τ (M.op X0 X0))
       have i₂ := eq2447924 X2 X0
       grind)
    | exact superpose eq2447924 eq61
    | exact resolve eq61 eq2447924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2447924
  have eq2711682 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2466111 X1 (M.op x X0) (σ X0)
       have i₂ := eq2417322 X0 X1 x
       grind)
    | exact superpose eq2417322 eq2466111
    | exact resolve eq2466111 eq2417322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417322 eq2466111
  have eq2714462 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq2711682 X0 X1
       grind)
    | exact superpose eq2711682 eq11
    | exact resolve eq11 eq2711682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711682
  have eq2723207 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2714462 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2714462
    | exact resolve eq2714462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714462
  have eq2727708 : False := by grind
  exact eq2727708

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq189 eq177
    | exact resolve eq177 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq812
       grind)
    | exact superpose eq812 eq41
    | exact resolve eq41 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq812
  have eq844 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq843
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq843
    | exact resolve eq843 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq846 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq844
    | exact resolve eq844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq846 eq817
    | exact resolve eq817 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq846
  have eq863 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq856
       have r₂ := eq27
       grind)
    | exact resolve eq856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq868 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq863 eq186
    | exact resolve eq186 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq869 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq863 eq190
    | exact resolve eq190 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq876 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq863 eq177
    | exact resolve eq177 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq911 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq869 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq869
       grind)
    | exact resolve eq13 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq911
  have eq924 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq868 eq923
    | exact resolve eq923 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq923
  have eq942 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq924 eq142
    | exact resolve eq142 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq943 : y = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32 eq942
    | exact resolve eq942 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq942
  have eq975 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq869 eq876
    | exact resolve eq876 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq876
  have eq992 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq975
  have eq997 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq992 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq992
       grind)
    | exact resolve eq13 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1008 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq997
  have eq1012 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1008 eq142
    | exact resolve eq142 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1008
  have eq1015 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1012
    | exact resolve eq1012 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1020 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq822 x
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq822
    | (have j0 := eq822 x
       grind)
    | (have r₁ := eq822 x
       have r₂ := eq1015
       grind)
    | exact resolve eq822 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1021 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq1020
  have eq1026 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq1021
       grind)
    | exact superpose eq1021 eq189
    | exact resolve eq189 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq177 y x X0
       have i₂ := eq1021
       grind)
    | exact superpose eq1021 eq177
    | exact resolve eq177 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1188 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1026 eq1033
    | exact resolve eq1033 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq1033
  have eq1205 : x = (M.op x x) := by grind
  clear eq1188
  have eq1208 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq1205
       grind)
    | exact superpose eq1205 eq189
    | exact resolve eq189 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1209 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1205
       grind)
    | exact superpose eq1205 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1205
       grind)
    | exact resolve eq13 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq178 x x x
       have i₂ := eq1205
       grind)
    | exact superpose eq1205 eq178
    | exact resolve eq178 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq192 x x x
       have i₂ := eq1205
       grind)
    | exact superpose eq1205 eq192
    | exact resolve eq192 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : x = (k x x) := by grind
  clear eq1209
  have eq1224 : x ≠ x ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1208 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1208
       grind)
    | exact resolve eq13 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1208 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1236 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq1224
  have eq1239 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1220
       grind)
    | exact superpose eq1220 eq40
    | exact resolve eq40 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1242 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1239
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1239
    | exact resolve eq1239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1247 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1242 eq822
    | (have j0 := eq822 (σ x)
       grind)
    | (have r₁ := eq822 (σ x)
       have r₂ := eq1242
       grind)
    | exact resolve eq822 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq1248 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1247
  have eq1262 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1248 eq178
    | exact resolve eq178 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1248 eq192
    | exact resolve eq192 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : ∀ X0 : G, x ≠ x ∨ (M.op (M.op x X0) x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x X0) x
       have i₂ := eq1214 X0
       grind)
    | exact superpose eq1214 eq13
    | (have j0 := eq13 (M.op x X0) x
       grind)
    | (have r₁ := eq13 (M.op x X0) x
       have r₂ := eq1214 X0
       grind)
    | exact resolve eq13 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1309 : ∀ X0 : G, (M.op (M.op x X0) x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq1297 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1313 : ∀ X0 : G, x = (M.op (k X0 x) x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1217 X0
       have i₂ := eq28 X0 x
       grind)
    | exact superpose eq28 eq1217
    | (have j1 := eq28 x (k X0 x)
       grind)
    | exact resolve eq1217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1341 : (M.op x y) = (M.op x (k (M.op x y) x)) := by
    first
    | exact superpose eq1236 eq209
    | exact resolve eq209 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1345 : (M.op x y) ≠ (k (M.op x y) x) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1236 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | exact resolve eq13 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1356 : (M.op x y) ≠ (k (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1208 eq1345
    | exact resolve eq1345 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1429 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1262 eq13
    | (have j0 := eq13 (M.op (σ x) X0) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) X0) (σ x)
       have r₂ := eq1262 X0
       grind)
    | exact resolve eq13 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1441 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1672 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1227 eq42
    | exact resolve eq42 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1673 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1672
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1672
    | exact resolve eq1672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1675 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1236 eq1673
    | exact resolve eq1673 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1681 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1675 eq164
    | exact resolve eq164 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq1675
  have eq1682 : x = (k (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq30 eq1681
    | exact resolve eq1681 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq1688 : (M.op x y) = (M.op x x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1682 eq1341
    | exact resolve eq1341 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1693 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1682 eq1356
    | exact resolve eq1356 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq1682
  have eq1697 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq1693
  have eq1700 : x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1688
       have i₂ := eq1205
       grind)
    | exact superpose eq1205 eq1688
    | exact resolve eq1688 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1702 : x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq1700
       have r₂ := eq1697
       grind)
    | exact resolve eq1700 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq1700
  have eq1907 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1702 eq42
    | exact resolve eq42 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1702
  have eq1910 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1907
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1907
    | exact resolve eq1907 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq1916 : (σ x) ≠ (σ x) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1910 eq778
    | (have j0 := eq778 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq778 (σ x) (σ (M.op x y))
       have r₂ := eq1910
       grind)
    | exact resolve eq778 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq1916
  have eq2095 : ∀ X0 : G, (M.op x X0) = (M.op x (k (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq178 x X0 x
       have i₂ := eq1309 X0
       grind)
    | exact superpose eq1309 eq178
    | exact resolve eq178 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2097 : ∀ X0 : G, (M.op X0 x) = (k (M.op x (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq192 x x X0
       have i₂ := eq1309 (M.op X0 x)
       grind)
    | exact superpose eq1309 eq192
    | exact resolve eq192 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2098 : ∀ X0 : G, x = (M.op (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1217 (M.op x X0)
       have i₂ := eq1309 X0
       grind)
    | exact superpose eq1309 eq1217
    | exact resolve eq1217 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq1309
  have eq2139 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) ∨ (k (M.op x X0) x) = (M.op x (k (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq28 (k (M.op x X0) x) x
       have i₂ := eq2098 X0
       grind)
    | exact superpose eq2098 eq28
    | (have j0 := eq28 (k (M.op x X0) x) x
       grind)
    | exact resolve eq28 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2153 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) x) ∨ x = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq2139 X0
       have i₂ := eq2095 X0
       grind)
    | exact superpose eq2095 eq2139
    | (have j0 := eq2139 X0
       grind)
    | exact resolve eq2139 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139
  have eq2268 : ∀ X0 : G, (M.op x X0) ≠ (k (M.op x X0) x) ∨ x = (M.op x X0) ∨ (M.op x x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq12 (k (M.op x X0) x) x
       have i₂ := eq2095 X0
       grind)
    | exact superpose eq2095 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2269 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op (k (M.op x X0) x) x) = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq13 (k (M.op x X0) x) x
       have i₂ := eq2095 X0
       grind)
    | exact superpose eq2095 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2285 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq2269 X0
       have i₂ := eq2098 X0
       grind)
    | exact superpose eq2098 eq2269
    | (have j0 := eq2269 X0
       grind)
    | exact resolve eq2269 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2286 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) ∨ (M.op x X0) ≠ (k (M.op x X0) x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2268 X0
       have i₂ := eq1205
       grind)
    | exact superpose eq1205 eq2268
    | (have j0 := eq2268 X0
       grind)
    | exact resolve eq2268 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq2268
  have eq2290 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) ∨ (M.op x X0) ≠ (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq2286 X0
       have j1 := eq2285 X0
       grind)
    | (have r₁ := eq2286 X0
       have r₂ := eq2285 X0
       grind)
    | exact resolve eq2286 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285 eq2286
  have eq2291 : ∀ X0 : G, x = (k (k (M.op x X0) x) x) := by
    intro X0
    first
    | (have j0 := eq2290 X0
       have j1 := eq2153 X0
       grind)
    | (have r₁ := eq2290 X0
       have r₂ := eq2153 X0
       grind)
    | exact resolve eq2290 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq2290
  have eq2354 : ∀ X0 : G, x = (k (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq2291 (M.op X0 x)
       have i₂ := eq2097 X0
       grind)
    | exact superpose eq2097 eq2291
    | exact resolve eq2291 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2358 : ∀ X0 : G, (k (σ (M.op x (M.op X0 x))) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq40 (M.op x (M.op X0 x))
       have i₂ := eq2097 X0
       grind)
    | exact superpose eq2097 eq40
    | exact resolve eq40 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097
  have eq2378 : ∀ X0 : G, (σ x) = (k (σ (M.op X0 x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 (M.op X0 x)
       have i₂ := eq2354 X0
       grind)
    | exact superpose eq2354 eq40
    | exact resolve eq40 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2380 : ∀ X0 : G, (σ x) = (k (σ (M.op X0 x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2378 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2378
    | (have j0 := eq2378 X0
       grind)
    | exact resolve eq2378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2479 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (k (M.op (σ x) X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq1441 eq178
    | exact resolve eq178 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2481 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (M.op X0 (σ x))) (σ x)) := by
    intro X0
    first
    | exact superpose eq1441 eq192
    | exact resolve eq192 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq2482 : ∀ X0 : G, (σ x) = (M.op (k (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1441 eq1265
    | exact resolve eq1265 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq2533 : ∀ X0 : G, (σ x) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) ∨ (k (M.op (σ x) X0) (σ x)) = (M.op (σ x) (k (M.op (σ x) X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq2482 eq28
    | (have j0 := eq28 (k (M.op (σ x) X0) (σ x)) (σ x)
       grind)
    | exact resolve eq28 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2547 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) ∨ (σ x) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2479 eq2533
    | (have j0 := eq2533 X0
       grind)
    | exact resolve eq2533 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq2856 : ∀ X0 : G, (M.op (σ x) X0) ≠ (k (M.op (σ x) X0) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ x)) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2479 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | exact resolve eq12 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (k (M.op (σ x) X0) (σ x)) (σ x)) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2479 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2874 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2482 eq2857
    | (have j0 := eq2857 X0
       grind)
    | exact resolve eq2857 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482 eq2857
  have eq2875 : ∀ X0 : G, (σ x) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) ∨ (M.op (σ x) X0) ≠ (k (M.op (σ x) X0) (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq1248 eq2856
    | (have j0 := eq2856 X0
       grind)
    | exact resolve eq2856 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq2856
  have eq2882 : ∀ X0 : G, (σ x) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) ∨ (M.op (σ x) X0) ≠ (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2875 X0
       have j1 := eq2874 X0
       grind)
    | (have r₁ := eq2875 X0
       have r₂ := eq2874 X0
       grind)
    | exact resolve eq2875 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq2875
  have eq2883 : ∀ X0 : G, (σ x) = (k (k (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2882 X0
       have j1 := eq2547 X0
       grind)
    | (have r₁ := eq2882 X0
       have r₂ := eq2547 X0
       grind)
    | exact resolve eq2882 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547 eq2882
  have eq2961 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2481 eq2883
    | exact resolve eq2883 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq2883
  have eq3232 : x = (M.op y x) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq943 eq1313
    | (have j0 := eq1313 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq1313 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq3273 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by grind
  clear eq3232
  have eq3282 : x = (M.op (k (τ (M.op (σ x) (σ y))) x) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3273 eq2098
    | exact resolve eq2098 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098 eq3273
  have eq3313 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq943 eq3282
    | exact resolve eq3282 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq3282
  have eq3314 : x = (M.op y x) := by grind
  clear eq3313
  have eq3319 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq185 x
       have i₂ := eq3314
       grind)
    | exact superpose eq3314 eq185
    | exact resolve eq185 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq3314
  have eq3352 : y = (k (M.op x y) x) := by
    first
    | exact superpose eq3319 eq1236
    | exact resolve eq1236 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq3355 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3319 eq2380
    | exact resolve eq2380 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380 eq3319
  have eq3382 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3355
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3355
    | exact resolve eq3355 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3396 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3352 eq40
    | exact resolve eq40 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq3401 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq3396
    | exact resolve eq3396 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396
  have eq3403 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq3401
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3401
    | exact resolve eq3401 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3401
  have eq3441 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3382 eq778
    | (have j0 := eq778 (σ y) (σ x)
       grind)
    | exact resolve eq778 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq3382
  have eq3443 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3441
    | exact resolve eq3441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq3448 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3443
    | exact resolve eq3443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq4587 : (σ x) = (M.op (k (σ (M.op x y)) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1917 eq1265
    | exact resolve eq1265 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq4596 : ∀ X0 : G, (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (k (σ (M.op x y)) (σ x)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1917 eq178
    | exact resolve eq178 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq4609 : (σ x) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq1917
  have eq4610 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3403 eq4609
    | exact resolve eq4609 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4609
  have eq4614 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq3403 eq4596
    | exact resolve eq4596 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596
  have eq4620 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3403 eq4587
    | exact resolve eq4587 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4658 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4620 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4620
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq4620
       grind)
    | exact resolve eq12 eq4620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4620
  have eq4678 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq4658
  have eq4679 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq4678
       have r₂ := eq4610
       grind)
    | exact resolve eq4678 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610 eq4678
  have eq5227 : (σ y) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4679 eq4614
    | exact resolve eq4614 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4614 eq4679
  have eq5253 : (σ y) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq5227
  have eq10020 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1910 eq782
    | (have j0 := eq782 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq782 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq1910
  have eq10506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq5253 eq10020
    | exact resolve eq10020 eq5253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253 eq10020
  have eq10563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq10506
  have eq10576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq10563
    | exact resolve eq10563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10563
  have eq10582 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq10576
       have r₂ := eq27
       grind)
    | exact resolve eq10576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10576
  have eq10603 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq10582 eq177
    | exact resolve eq177 eq10582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq10582
  have eq10644 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq10603 eq2961
    | exact resolve eq2961 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961 eq10603
  have eq10707 : (σ x) = (σ y) := by
    first
    | exact superpose eq10644 eq3403
    | exact resolve eq3403 eq10644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq10710 : (τ (σ x)) = (k (M.op x y) x) := by
    first
    | exact superpose eq10644 eq132
    | exact resolve eq132 eq10644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq10644
  have eq10725 : y = (τ (σ x)) := by
    first
    | exact superpose eq3352 eq10710
    | exact resolve eq10710 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq10710
  have eq10727 : x = y := by
    first
    | exact superpose eq30 eq10725
    | exact resolve eq10725 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10725
  have eq10759 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10707 eq3448
    | (have r₁ := eq3448
       have r₂ := eq10707
       grind)
    | exact resolve eq3448 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448 eq10707
  have eq10797 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10759
  have eq10801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1242 eq10797
    | exact resolve eq10797 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10797
  have eq10802 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10801
  have eq10820 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10727
       grind)
    | exact superpose eq10727 eq18
    | exact resolve eq18 eq10727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10727
  have eq10880 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq10802 eq27
    | exact resolve eq27 eq10802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10802
  have eq11057 : (σ (M.op x y)) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq2358 x
       have i₂ := eq10820
       grind)
    | exact superpose eq10820 eq2358
    | exact resolve eq2358 eq10820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358 eq10820
  have eq11086 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1208 eq11057
    | exact resolve eq11057 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq11057
  have eq11089 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11086
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11086
    | exact resolve eq11086 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11086
  have eq11090 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1242 eq11089
    | exact resolve eq11089 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242 eq11089
  have eq11446 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11090 eq20
    | exact resolve eq20 eq11090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11090
  have eq11515 : False := by grind
  exact eq11515

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28
    | exact resolve eq28 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq34 : (M.op x y) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32
       grind)
    | exact superpose eq32 eq19
    | exact resolve eq19 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq32
  have eq36 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq34
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq34
    | exact resolve eq34 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X1 X4 X5 : G, (M.op (M.op X1 X4) (M.op X4 X5)) = X4 := by
    intro X1 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X1) (M.op X1 x) X5
       have i₂ := eq9 X1 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X1 X3 X4 : G, (M.op X1 X3) = (M.op X1 (M.op (M.op X1 X3) X4)) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 X3) (M.op x x) X1 X4
       have i₂ := eq9 X1 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq36 eq41
    | exact resolve eq41 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq36 eq41
    | exact resolve eq41 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X3 (M.op X2 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq41 X3 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq41 X2 X0 x
       grind)
    | exact superpose eq41 eq41
    | exact resolve eq41 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq61 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq60 X0
       have j1 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq60 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq61 (M.op X0 X0)
       have i₂ := eq41 X0 X0 X0
       grind)
    | exact superpose eq41 eq61
    | exact resolve eq61 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq36 eq14
    | (have j0 := eq14 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k (M.op X2 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X0 X1)
       have i₂ := eq41 X2 X0 X1
       grind)
    | exact superpose eq41 eq14
    | (have j0 := eq14 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq104 : ∀ X0 : G, (M.op x y) = (M.op (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) ∨ (τ (σ y)) = (k (M.op x y) (M.op (τ (σ y)) X0)) ∨ (M.op (τ (σ y)) X0) = (M.op (M.op (τ (σ y)) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | (have j0 := eq14 (M.op x y) (M.op (τ (σ y)) X0)
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X1 : G, (M.op x y) = (M.op (M.op X1 (M.op x y)) (τ (σ y))) := by
    intro X1
    first
    | exact superpose eq55 eq41
    | exact resolve eq41 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (M.op x y) = (M.op (τ (σ x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq36 eq42
    | exact resolve eq42 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = X1 ∨ (M.op X1 X2) = (k X1 (M.op (M.op X1 X2) X0)) ∨ (M.op (M.op X1 X2) X0) = (M.op (M.op (M.op X1 X2) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X2) X0)
       have i₂ := eq42 X1 X2 X0
       grind)
    | exact superpose eq42 eq14
    | (have j0 := eq14 X1 (M.op (M.op X1 X2) X0)
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) ∨ (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq126 eq14
    | (have j0 := eq14 (τ (σ x)) (M.op (M.op x y) X0)
       grind)
    | exact resolve eq14 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 X0) X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq233 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (M.op (τ (σ y)) X0)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq66 eq42
    | exact resolve eq42 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ y)) (M.op (τ (σ x)) X0)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq66 eq41
    | exact resolve eq41 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq66 eq12
    | (have j0 := eq12 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq12 (τ (σ x)) (τ (σ y))
       have r₂ := eq66
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq238 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by grind
  clear eq237
  have eq544 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq238 eq15
    | exact resolve eq15 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq551 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq544
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq544
    | exact resolve eq544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq552 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq551
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq602 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq233 eq233
    | exact resolve eq233 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq623 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by grind
  clear eq602
  have eq715 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq236 eq55
    | exact resolve eq55 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq759 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq183 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq183
    | exact resolve eq183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq866 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X0 X1
       have i₂ := eq41 X0 X0 X0
       grind)
    | exact superpose eq41 eq67
    | (have j0 := eq67 X0 X0 X1
       grind)
    | exact resolve eq67 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op X1 X2) (M.op X1 X2))) = X0 ∨ (k (M.op X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41 X3 X0 X1
       have i₂ := eq67 X1 X2 X0
       grind)
    | exact superpose eq67 eq41
    | (have j1 := eq67 X1 X2 X0
       grind)
    | exact resolve eq41 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (k (M.op X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X2) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X1 X2 (M.op X1 X2)
       have i₂ := eq67 X1 X2 X0
       grind)
    | exact superpose eq67 eq42
    | (have j1 := eq67 X1 X2 X0
       grind)
    | exact resolve eq42 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X2)) ∨ (k (M.op X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op X0 X1)
       have i₂ := eq67 X0 X1 X2
       grind)
    | exact superpose eq67 eq64
    | (have j1 := eq67 X1 X2 X0
       grind)
    | exact resolve eq64 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X1 X2)) (M.op X0 X1)) ∨ (k (M.op X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41 X3 (M.op X1 X2) (M.op X1 X2)
       have i₂ := eq67 X1 X2 X0
       grind)
    | exact superpose eq67 eq41
    | (have j1 := eq67 X1 X2 X0
       grind)
    | exact resolve eq41 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq923 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X2)) ∨ (k (M.op X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq898 X0 X1 X2
       have j1 := eq12 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have r₁ := eq898 X0 X1 X2
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X2)
       grind)
    | exact resolve eq898 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq1203 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op (M.op X2 X0) X1) X2) ∨ (M.op X2 X0) = (k X2 (M.op (M.op X2 X0) X1)) ∨ (M.op (M.op X2 X0) X1) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 (M.op X2 X0) X1 (M.op (M.op X2 X0) X1)
       have i₂ := eq131 X1 X2 X0
       grind)
    | exact superpose eq131 eq42
    | (have j1 := eq131 X1 X2 X0
       grind)
    | exact resolve eq42 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (k (M.op (M.op X2 X0) X1) X2) ∨ (M.op X2 X0) = (k X2 (M.op (M.op X2 X0) X1)) ∨ (M.op (M.op X2 X0) X1) = (M.op (M.op (M.op X2 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op (M.op X2 X0) X1)
       have i₂ := eq131 X1 X2 X0
       grind)
    | exact superpose eq131 eq61
    | (have j1 := eq131 X1 X2 X0
       grind)
    | exact resolve eq61 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op (M.op X2 X0) X1) X2) ∨ (M.op X2 X0) = (k X2 (M.op (M.op X2 X0) X1)) ∨ (M.op (M.op X3 X2) (M.op (M.op X2 X0) X1)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq131 X0 X1 X2
       grind)
    | exact superpose eq131 eq58
    | (have j1 := eq131 X1 X2 X0
       grind)
    | exact resolve eq58 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq2014 : (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) ∨ (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq715 eq55
    | exact resolve eq55 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq715
  have eq2041 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) := by grind
  clear eq2014
  have eq2078 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq623
       have i₂ := eq14 (τ sF3) (τ sF3)
       grind)
    | exact superpose eq14 eq623
    | (have j1 := eq14 (τ (σ y)) (τ (σ y))
       grind)
    | exact resolve eq623 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq2118 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by grind
  clear eq2078
  have eq2122 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have j1 := eq12 (τ (σ y)) (τ (σ y))
       grind)
    | (have r₁ := eq2118
       have r₂ := eq12 (τ (σ y)) (τ (σ y))
       grind)
    | exact resolve eq2118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2187 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq2041 eq15
    | exact resolve eq15 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2194 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | (have i₁ := eq2187
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq2187
    | exact resolve eq2187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq2195 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | (have i₁ := eq2194
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq2194
    | exact resolve eq2194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq2196 : (τ (σ y)) = (M.op (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2195
    | exact resolve eq2195 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2280 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq57 eq866
    | exact resolve eq866 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2307 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1 (M.op X0 X0)
       have i₂ := eq866 X0 X1
       grind)
    | exact superpose eq866 eq58
    | (have j1 := eq866 X0 X1
       grind)
    | exact resolve eq58 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2311 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X0)) ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X2 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq866 X0 X1
       grind)
    | exact superpose eq866 eq41
    | (have j1 := eq866 X0 X1
       grind)
    | exact resolve eq41 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2312 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (M.op X0 X0) (M.op X1 X0) X2
       have i₂ := eq866 X0 X1
       grind)
    | exact superpose eq866 eq41
    | (have j1 := eq866 X0 X1
       grind)
    | exact resolve eq41 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq2386 : (τ (σ x)) = (M.op (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2196 eq57
    | exact resolve eq57 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq2624 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) ∨ (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq143 eq64
    | (have j1 := eq143 X0
       grind)
    | exact resolve eq64 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq2672 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq2624 X0
       have j1 := eq12 (τ (σ x)) (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq2624 X0
       have r₂ := eq12 (τ (σ x)) (M.op (M.op x y) X0)
       grind)
    | exact resolve eq2624 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq3301 : ∀ X1 : G, (M.op x y) = (M.op (τ (σ x)) (M.op X1 (τ (σ x)))) ∨ (τ (σ x)) = (k (M.op X1 (τ (σ x))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op X1 (τ (σ x)))) := by
    intro X1
    first
    | exact superpose eq126 eq892
    | exact resolve eq892 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq892
  have eq3716 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (τ (σ y)) X0)) ∨ (τ (σ y)) = (k (M.op x y) (M.op (τ (σ y)) X0)) ∨ (M.op (τ (σ y)) X0) = (M.op (M.op (τ (σ y)) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq104 eq64
    | (have j1 := eq104 X0
       grind)
    | exact resolve eq64 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq3780 : ∀ X0 : G, (τ (σ y)) = (k (M.op x y) (M.op (τ (σ y)) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have j0 := eq3716 X0
       have j1 := eq12 (M.op x y) (M.op (τ (σ y)) X0)
       grind)
    | (have r₁ := eq3716 X0
       have r₂ := eq12 (M.op x y) (M.op (τ (σ y)) X0)
       grind)
    | exact resolve eq3716 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq4926 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X0 X3)) ∨ (k (M.op X0 X3) (M.op X3 X2)) = X3 ∨ (M.op X0 X3) = (M.op (M.op X3 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq58 X3 X0 (M.op x (M.op X3 X2))
       have i₂ := eq902 X0 X3 X2 x
       grind)
    | exact superpose eq902 eq58
    | (have j1 := eq902 X0 X3 X2 X3
       grind)
    | exact resolve eq58 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq7046 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X2) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1203 x (M.op x x) x
       have i₂ := eq41 x x x
       grind)
    | exact superpose eq41 eq1203
    | exact resolve eq1203 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq7529 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1219 x (M.op x x) x X3
       have i₂ := eq41 x x x
       grind)
    | exact superpose eq41 eq1219
    | exact resolve eq1219 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq7692 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq552 eq759
    | exact resolve eq759 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq759
  have eq7723 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq7692
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq7692
    | exact resolve eq7692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7692
  have eq7724 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq7723
  have eq7888 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq7724 eq15
    | exact resolve eq15 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7724
  have eq7900 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7888
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq7888
    | exact resolve eq7888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq7901 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7900
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq7900
    | exact resolve eq7900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7900
  have eq7902 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq7901
    | exact resolve eq7901 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7901
  have eq9010 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X0 X2) = X0 ∨ (M.op X0 X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1205 x (M.op x x) x
       have i₂ := eq41 x x x
       grind)
    | exact superpose eq41 eq1205
    | exact resolve eq1205 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq16404 : ∀ X0 : G, (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2672 eq15
    | (have j1 := eq2672 X0
       grind)
    | exact resolve eq15 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16419 : ∀ X0 : G, (M.op x y) ≠ (τ (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq2672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16422 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16404 X0
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq16404
    | (have j0 := eq16404 X0
       grind)
    | exact resolve eq16404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16404
  have eq16866 : ∀ X0 : G, (σ (τ (σ y))) = (k (σ (M.op x y)) (σ (M.op (τ (σ y)) X0))) ∨ (M.op x y) = (k (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq3780 eq15
    | (have j1 := eq3780 X0
       grind)
    | exact resolve eq15 eq3780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780
  have eq16882 : ∀ X0 : G, (σ (τ (σ y))) = (k (σ (M.op x y)) (σ (M.op (τ (σ y)) X0))) ∨ (M.op x y) = (k (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq21 eq16866
    | (have j0 := eq16866 X0
       grind)
    | exact resolve eq16866 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866
  have eq16891 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ (M.op (τ (σ y)) X0))) ∨ (M.op x y) = (k (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq16882 X0
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq16882
    | (have j0 := eq16882 X0
       grind)
    | exact resolve eq16882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16882
  have eq17427 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq9010 X1 X0
       grind)
    | exact superpose eq9010 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq9010 X1 X0
       grind)
    | (have r₁ := eq12 x X0
       have r₂ := eq9010 X0 x
       grind)
    | exact resolve eq12 eq9010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9010
  have eq17684 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17427 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17427
  have eq19624 : (σ y) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2386 eq16891
    | exact resolve eq16891 eq2386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386 eq16891
  have eq19685 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq19624
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq19624
    | exact resolve eq19624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19624
  have eq20759 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq19685 eq15
    | exact resolve eq15 eq19685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19685
  have eq20784 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq20759
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq20759
    | exact resolve eq20759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq20785 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20784
    | exact resolve eq20784 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20784
  have eq20809 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  have eq45444 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op x x)
       have i₂ := eq7529 (M.op x x) x x
       grind)
    | exact superpose eq7529 eq64
    | (have j1 := eq7529 (M.op X1 X0) X0 x
       grind)
    | exact resolve eq64 eq7529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq45642 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45444 X0 X1
       have j1 := eq12 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq45444 X0 X1
       have r₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq45444 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45444
  have eq45678 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45642 x (M.op x X0)
       have i₂ := eq7046 X0 x
       grind)
    | exact superpose eq7046 eq45642
    | (have j1 := eq7046 X1 X0
       grind)
    | exact resolve eq45642 eq7046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046 eq45642
  have eq46071 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45678 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45678
  have eq46197 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46071 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46071 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46071 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46071
  have eq46787 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X2 X0 X1
       have i₂ := eq46197 X0 X1
       grind)
    | exact superpose eq46197 eq41
    | (have j1 := eq46197 X0 X1
       grind)
    | exact resolve eq41 eq46197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48595 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20785 eq46787
    | (have j0 := eq46787 (σ (M.op x y)) (σ x) x
       grind)
    | exact resolve eq46787 eq20785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20785
  have eq48765 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq48595 X0
       grind)
    | (have r₁ := eq48595 X0
       have r₂ := eq20809
       grind)
    | exact resolve eq48595 eq20809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20809 eq48595
  have eq64595 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq923 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq64811 : ∀ X0 : G, (M.op x y) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq36 eq64595
    | exact resolve eq64595 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70114 : (τ (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2280 eq57
    | exact resolve eq57 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq70395 : (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have j1 := eq16419 (M.op x y)
       grind)
    | (have r₁ := eq70114
       have r₂ := eq16419 x
       grind)
    | exact resolve eq70114 eq16419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16419 eq70114
  have eq70492 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq70395 eq15
    | exact resolve eq15 eq70395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70395
  have eq70521 : (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq70492
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq70492
    | exact resolve eq70492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70492
  have eq70524 : (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq21 eq70521
    | exact resolve eq70521 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70521
  have eq71157 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq2122 eq15
    | exact resolve eq15 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq71204 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq71157
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq71157
    | exact resolve eq71157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71157
  have eq72054 : (τ (σ y)) = (k (M.op x y) (M.op (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (M.op (M.op (τ (σ y)) (τ (σ y))) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq36 eq2307
    | exact resolve eq2307 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq72350 : (τ (σ y)) = (k (M.op x y) (M.op (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (M.op (M.op (τ (σ y)) (τ (σ y))) (τ (σ y))) := by
    first
    | (have j1 := eq64811 (τ (σ y))
       grind)
    | (have r₁ := eq72054
       have r₂ := eq64811 x
       grind)
    | exact resolve eq72054 eq64811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64811 eq72054
  have eq86964 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X1) ∨ (k (M.op X2 X1) (M.op X1 X1)) = X1 ∨ (M.op X2 X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq58 X1 X1 (M.op x (M.op X1 X1))
       have i₂ := eq2311 X1 X2 x
       grind)
    | exact superpose eq2311 eq58
    | (have j1 := eq2311 X1 X2 X2
       grind)
    | exact resolve eq58 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311
  have eq87181 : ∀ X1 X2 : G, (k (M.op X2 X1) (M.op X1 X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X1) := by
    intro X1 X2
    first
    | (have j0 := eq86964 X1 X2
       have j1 := eq64595 X2 X1 X1
       grind)
    | (have r₁ := eq86964 X1 x
       have r₂ := eq64595 x X1 X2
       grind)
    | exact resolve eq86964 eq64595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86964
  have eq87767 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (M.op X1 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 X0)) ∨ (k (M.op X0 X1) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X1 X0 X1 X1
       have i₂ := eq2312 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq2312 eq871
    | (have j0 := eq871 X1 X0 X1 x
       have j1 := eq2312 X1 X0 x
       grind)
    | exact resolve eq871 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq2312
  have eq87969 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (M.op X1 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 X0)) ∨ (k (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87767 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87767
  have eq88095 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 X0)) ∨ (k (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87969 X0 X1
       have j1 := eq64595 X1 X0 X1
       grind)
    | (have r₁ := eq87969 X0 X1
       have r₂ := eq64595 X0 X1 x
       grind)
    | (have r₁ := eq87969 X0 X0
       have r₂ := eq64595 (M.op X0 X0) (M.op X0 X0) x
       grind)
    | exact resolve eq87969 eq64595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87969
  have eq88402 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (M.op X1 X0) (M.op X0 X1)) = X0 ∨ (k (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88095 X0 X1
       have i₂ := eq41 X0 X1 X0
       grind)
    | (have i₁ := eq88095 X0 X1
       have i₂ := eq41 X1 (M.op (M.op X0 X1) (M.op X1 X0)) x
       grind)
    | exact superpose eq41 eq88095
    | (have j0 := eq88095 X0 X1
       grind)
    | exact resolve eq88095 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88095
  have eq88444 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X1)) = X0 ∨ (k (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88402 X0 X1
       have j1 := eq64595 X1 X0 X1
       grind)
    | (have r₁ := eq88402 X0 X1
       have r₂ := eq64595 X0 X1 x
       grind)
    | exact resolve eq88402 eq64595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64595 eq88402
  have eq95672 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq88444 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88444
  have eq95673 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq95672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95672
  have eq96118 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq95673 (M.op x x)
       have i₂ := eq41 x x x
       grind)
    | exact superpose eq41 eq95673
    | exact resolve eq95673 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96298 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq61
    | exact resolve eq61 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq103181 : ∀ X1 X2 : G, (k (M.op X2 X1) (k X1 X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq87181 X1 X2
       have i₂ := eq96118 X1
       grind)
    | exact superpose eq96118 eq87181
    | (have j0 := eq87181 X1 X2
       grind)
    | exact resolve eq87181 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87181
  have eq104058 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq95673 X0
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq95673
    | exact resolve eq95673 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95673
  have eq113160 : (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (M.op (M.op (τ (σ y)) (τ (σ y))) (τ (σ y))) := by
    first
    | (have i₁ := eq72350
       have i₂ := eq96118 (τ sF3)
       grind)
    | exact superpose eq96118 eq72350
    | exact resolve eq72350 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72350
  have eq115505 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq70524
       have i₂ := eq96118 sF0
       grind)
    | exact superpose eq96118 eq70524
    | exact resolve eq70524 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70524
  have eq116663 : (σ (M.op x y)) = (k (σ x) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq115505
       have i₂ := eq96118 sF0
       grind)
    | exact superpose eq96118 eq115505
    | exact resolve eq115505 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115505
  have eq117759 : (M.op x y) = (M.op (k (τ (σ y)) (τ (σ y))) (τ (σ y))) ∨ (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq113160
       have i₂ := eq96118 (τ sF3)
       grind)
    | exact superpose eq96118 eq113160
    | exact resolve eq113160 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113160
  have eq124376 : ∀ X1 X2 : G, (k (M.op X2 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = (M.op (k X1 X1) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq103181 x X2
       have i₂ := eq96118 x
       grind)
    | exact superpose eq96118 eq103181
    | (have j0 := eq103181 X1 X2
       grind)
    | exact resolve eq103181 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103181
  have eq129166 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq116663
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq116663
    | exact resolve eq116663 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116663
  have eq136520 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq129166
    | exact resolve eq129166 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129166
  have eq153765 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 X0 X0
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq41
    | exact resolve eq41 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq153767 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X0 x
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq42
    | exact resolve eq42 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq153769 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X0 x
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq58
    | exact resolve eq58 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153826 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (k X0 X0) X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7529 X1 X0 X0
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq7529
    | (have j0 := eq7529 X1 X0 x
       grind)
    | exact resolve eq7529 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7529
  have eq153832 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X1)) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46787 X0 X1 X0
       have i₂ := eq96118 X0
       grind)
    | exact superpose eq96118 eq46787
    | (have j0 := eq46787 X0 X1 x
       grind)
    | exact resolve eq46787 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153846 : (τ (σ x)) = (M.op (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | (have i₁ := eq57 (τ sF2)
       have i₂ := eq96118 (τ sF2)
       grind)
    | exact superpose eq96118 eq57
    | exact resolve eq57 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq153865 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have i₁ := eq105 sF0
       have i₂ := eq96118 sF0
       grind)
    | exact superpose eq96118 eq105
    | exact resolve eq105 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153921 : (τ (σ x)) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2672 sF0
       have i₂ := eq96118 sF0
       grind)
    | exact superpose eq96118 eq2672
    | exact resolve eq2672 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq153923 : (σ x) = (k (σ x) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16422 sF0
       have i₂ := eq96118 sF0
       grind)
    | exact superpose eq96118 eq16422
    | exact resolve eq16422 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16422
  have eq153928 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153923
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq153923
    | exact resolve eq153923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153923
  have eq154016 : (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (σ x) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq153928
    | exact resolve eq153928 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153928
  have eq155111 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x)))) := by
    first
    | (have i₁ := eq3301 (k (τ sF2) (τ sF2))
       have i₂ := eq153767 (τ sF2) (τ sF2)
       grind)
    | exact superpose eq153767 eq3301
    | (have j0 := eq3301 (k (τ (σ x)) (τ (σ x)))
       grind)
    | exact resolve eq3301 eq153767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3301
  have eq156646 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ x) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq154016 eq15
    | exact resolve eq15 eq154016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154016
  have eq156655 : (σ (M.op x y)) = (k (σ (τ (σ x))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq156646
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq156646
    | exact resolve eq156646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156646
  have eq156656 : (σ (M.op x y)) = (k (σ (τ (σ x))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq156655
    | exact resolve eq156655 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156655
  have eq156657 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq156656
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq156656
    | exact resolve eq156656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156656
  have eq156661 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by grind
  have eq158484 : (M.op x y) ≠ (τ (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by grind
  clear eq153921
  have eq180817 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq71204 eq15
    | exact resolve eq15 eq71204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71204
  have eq180829 : (σ (τ (σ x))) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq180817
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq180817
    | exact resolve eq180817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180817
  have eq180831 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq180829
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq180829
    | exact resolve eq180829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180829
  have eq181725 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq180831 eq15
    | exact resolve eq15 eq180831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180831
  have eq181760 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq181725
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq181725
    | exact resolve eq181725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181725
  have eq181761 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq181760
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq181760
    | exact resolve eq181760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181760
  have eq181762 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq181761
    | exact resolve eq181761 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181761
  have eq196894 : (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq117759 eq124376
    | exact resolve eq124376 eq117759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117759 eq124376
  have eq196911 : (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq196894
  have eq197388 : (σ (τ (σ y))) = (k (σ (M.op x y)) (σ (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq196911 eq15
    | exact resolve eq15 eq196911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196911
  have eq197428 : (σ (τ (σ y))) = (k (σ (M.op x y)) (k (σ (τ (σ y))) (σ (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq197388
       have i₂ := eq15 (τ sF3) (τ sF3)
       grind)
    | exact superpose eq15 eq197388
    | exact resolve eq197388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197388
  have eq197434 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq197428
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq197428
    | exact resolve eq197428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197428
  have eq197436 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq21 eq197434
    | exact resolve eq197434 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197434
  have eq197455 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq197436 eq46787
    | exact resolve eq46787 eq197436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197483 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq197436 eq153832
    | exact resolve eq153832 eq197436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153832 eq197436
  have eq232691 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X0) X2) ∨ (k (M.op X1 X2) (M.op X2 X0)) = X2 ∨ (M.op X1 X2) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X2 X1 (M.op X2 X0)
       have i₂ := eq4926 X1 X0 X2
       grind)
    | exact superpose eq4926 eq58
    | (have j1 := eq4926 X1 X0 X2
       grind)
    | exact resolve eq58 eq4926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq4926
  have eq232877 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) (M.op X2 X0)) = X2 ∨ (M.op X1 X2) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq232691 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232691
  have eq236625 : ∀ X0 : G, (M.op x y) = (k (τ (σ x)) (M.op (M.op x y) X0)) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq153846 eq232877
    | exact resolve eq232877 eq153846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232877
  have eq238528 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op (M.op x y) X0))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq236625 eq15
    | (have j1 := eq236625 X0
       grind)
    | exact resolve eq15 eq236625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236625
  have eq238579 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq238528 X0
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq238528
    | (have j0 := eq238528 X0
       grind)
    | exact resolve eq238528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238528
  have eq238582 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq238579
    | (have j0 := eq238579 X0
       grind)
    | exact resolve eq238579 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238579
  have eq239810 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (M.op X1 (σ x)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq238582 eq46787
    | (have j1 := eq238582 X0
       grind)
    | exact resolve eq46787 eq238582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46787 eq238582
  have eq252224 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f252224_14 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op X1 (σ x)) (σ (M.op x y))) := by
      intro X0 X1
      grind
    have f252224_15 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) := by
      intro X0 X1
      grind
    have f252224_17 : ∀ X0 : G, (τ (σ X0)) = X0 := by
      intro X0
      grind
    have f252224_24 : (σ x) ≠ (M.op (M.op X0 (σ x)) (σ (M.op x y))) := by grind
    have f252224_25 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f252224_26 : (τ (σ x)) ≠ (k (M.op x y) (M.op x y)) := by grind
    have f252224_28 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (M.op (M.op X1 (σ x)) (σ (M.op x y))) := by
      intro X0 X1
      first
      | (have j0 := f252224_14 X0 X1
         grind)
      | (have r₁ := f252224_14 X0 X1
         have r₂ := f252224_25
         grind)
      | exact resolve f252224_14 f252224_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f252224_29 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (M.op (M.op X1 (σ x)) (σ (M.op x y))) := by
      intro X0 X1
      first
      | (have i₁ := f252224_28 X0 X1
         have i₂ := f252224_17 x
         grind)
      | exact superpose f252224_17 f252224_28
      | (have j0 := f252224_28 X0 X1
         grind)
      | exact resolve f252224_28 f252224_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f252224_132 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
      intro X0
      first
      | (have i₁ := f252224_15 (M.op x y) (M.op x y)
         have i₂ := f252224_29 (k (M.op x y) (M.op x y)) X0
         grind)
      | exact superpose f252224_29 f252224_15
      | (have j1 := f252224_29 X0 X0
         grind)
      | exact resolve f252224_15 f252224_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f252224_819 : (σ x) ≠ (σ x) ∨ x = (k (M.op x y) (M.op x y)) := by
      first
      | (have i₁ := f252224_24
         have i₂ := f252224_132 X0
         grind)
      | exact superpose f252224_132 f252224_24
      | (have r₁ := f252224_24
         have r₂ := f252224_132 X0
         grind)
      | exact resolve f252224_24 f252224_132
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f252224_839 : x = (k (M.op x y) (M.op x y)) := by grind
    have f252224_843 : x ≠ (τ (σ x)) := by
      first
      | (have i₁ := f252224_26
         have i₂ := f252224_839
         grind)
      | exact superpose f252224_839 f252224_26
      | exact resolve f252224_26 f252224_839
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f252224_857 : False := by
      first
      | (have r₁ := f252224_843
         have r₂ := f252224_17 x
         grind)
      | exact resolve f252224_843 f252224_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f252224_857
  clear eq153769 eq239810
  have eq253055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq252224 eq197455
    | exact resolve eq197455 eq252224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197455
  have eq253056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq252224 eq48765
    | exact resolve eq48765 eq252224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48765 eq252224
  have eq253234 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq253056
       have r₂ := eq29
       grind)
    | exact resolve eq253056 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253056
  have eq253235 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq253055
       have r₂ := eq29
       grind)
    | exact resolve eq253055 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253055
  have eq254257 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq253234 eq11
    | exact resolve eq11 eq253234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253234
  have eq254281 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq254257
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq254257
    | exact resolve eq254257 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254257
  have eq254311 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq254281
    | exact resolve eq254281 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254281
  have eq254329 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq254311 eq96298
    | exact resolve eq96298 eq254311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96298 eq254311
  have eq254417 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq254329
  have eq254439 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq254417 eq29
    | exact resolve eq29 eq254417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254484 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq254417
  have eq254523 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq254439
       have i₂ := eq46197 sF2 sF3
       grind)
    | exact superpose eq46197 eq254439
    | (have j1 := eq46197 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq254439
       have r₂ := eq46197 (σ x) (σ y)
       grind)
    | exact resolve eq254439 eq46197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254439
  have eq254536 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq254523
  have eq254540 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq254536
       have r₂ := eq254484
       grind)
    | exact resolve eq254536 eq254484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254484 eq254536
  have eq254546 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq254540 eq188
    | exact resolve eq188 eq254540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254540
  have eq254584 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq254546
    | exact resolve eq254546 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254546
  have eq254602 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq254584 eq17684
    | (have j0 := eq17684 (M.op x y) (τ (σ x))
       grind)
    | (have r₁ := eq17684 (M.op x y) (τ (σ x))
       have r₂ := eq254584
       grind)
    | exact resolve eq17684 eq254584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17684 eq254584
  have eq254633 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq254602
  have eq255051 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq254633 eq15
    | exact resolve eq15 eq254633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254633
  have eq255091 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq255051
    | exact resolve eq255051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255051
  have eq255093 : (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq255091
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq255091
    | exact resolve eq255091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255091
  have eq257201 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq255093 eq46197
    | (have j0 := eq46197 (τ (σ x)) (M.op x y)
       grind)
    | exact resolve eq46197 eq255093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255093
  have eq257300 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq257201
  have eq257375 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq257300 eq15
    | exact resolve eq15 eq257300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257300
  have eq257415 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq257375
    | exact resolve eq257375 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257375
  have eq257417 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq257415
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq257415
    | exact resolve eq257415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257415
  have eq257418 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq257417
  have eq260699 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq253235 eq15
    | exact resolve eq15 eq253235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253235
  have eq260730 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq260699
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq260699
    | exact resolve eq260699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260699
  have eq260744 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq260730
    | exact resolve eq260730 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260730
  have eq260933 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq260744 eq11
    | exact resolve eq11 eq260744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260744
  have eq260953 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq260933
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq260933
    | exact resolve eq260933 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260933
  have eq260993 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq260953
    | exact resolve eq260953 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260953
  have eq261013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq260993 eq197483
    | exact resolve eq197483 eq260993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197483 eq260993
  have eq261110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq261013
  have eq261130 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq261110
       have r₂ := eq29
       grind)
    | exact resolve eq261110 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261110
  have eq267610 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq261130 eq15
    | exact resolve eq15 eq261130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261130
  have eq267644 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq267610
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq267610
    | exact resolve eq267610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267610
  have eq267664 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq267644
    | exact resolve eq267644 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267644
  have eq267665 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq267664
  have eq267672 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq267665 eq29
    | exact resolve eq29 eq267665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267690 : (σ x) = (k (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (k (σ y) (σ y)) = (k (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq267665 eq156657
    | exact resolve eq156657 eq267665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156657
  have eq267747 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq267748 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq267665
  have eq267778 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq267690
       have i₂ := eq104058 sF3
       grind)
    | exact superpose eq104058 eq267690
    | exact resolve eq267690 eq104058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267690
  have eq267804 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq267778
       have i₂ := eq104058 sF3
       grind)
    | exact superpose eq104058 eq267778
    | exact resolve eq267778 eq104058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104058 eq267778
  have eq267819 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq181762 eq267747
    | (have r₁ := eq267747
       have r₂ := eq181762
       grind)
    | exact resolve eq267747 eq181762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181762 eq267747
  have eq267820 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq267819
  have eq267824 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq267820
       have r₂ := eq267748
       grind)
    | exact resolve eq267820 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267748 eq267820
  have eq267903 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq267824
  have eq267971 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq267672
       have i₂ := eq46197 sF2 sF3
       grind)
    | exact superpose eq46197 eq267672
    | (have j1 := eq46197 (σ x) (σ y)
       grind)
    | exact resolve eq267672 eq46197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46197 eq267672
  have eq267985 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq267971
       have r₂ := eq267804
       grind)
    | exact resolve eq267971 eq267804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267804 eq267971
  have eq267990 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq267985
       have r₂ := eq267903
       grind)
    | exact resolve eq267985 eq267903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267903 eq267985
  have eq268000 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq267990 eq30
    | exact resolve eq30 eq267990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267990
  have eq268093 : (M.op x y) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq268000 eq36
    | exact resolve eq36 eq268000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq268244 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq268000 eq153865
    | exact resolve eq153865 eq268000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153865
  have eq269234 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq268093 eq105
    | exact resolve eq105 eq268093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq268093
  have eq269507 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq268000 eq269234
    | exact resolve eq269234 eq268000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268000 eq269234
  have eq269758 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq269507
  have eq269779 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq269758
       have i₂ := eq96118 sF0
       grind)
    | exact superpose eq96118 eq269758
    | exact resolve eq269758 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269758
  have eq269867 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq269779 eq15
    | exact resolve eq15 eq269779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269779
  have eq269888 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq269867
    | exact resolve eq269867 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269867
  have eq273795 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq268244 eq136520
    | exact resolve eq136520 eq268244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136520 eq268244
  have eq274054 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq273795
       have r₂ := eq156661
       grind)
    | exact resolve eq273795 eq156661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156661 eq273795
  have eq279351 : (τ (σ (M.op x y))) = (k (τ (σ x)) (τ (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq274054 eq188
    | exact resolve eq188 eq274054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274054
  have eq279407 : (τ (σ (M.op x y))) = (k (τ (σ x)) (k (τ (σ (M.op x y))) (τ (σ (M.op x y))))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq279351
       have i₂ := eq188 sF1 sF1
       grind)
    | exact superpose eq188 eq279351
    | exact resolve eq279351 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq279351
  have eq279411 : (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq30 eq279407
    | exact resolve eq279407 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279407
  have eq279413 : (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq279411
       have r₂ := eq158484
       grind)
    | exact resolve eq279411 eq158484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158484 eq279411
  have eq279437 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq279413 eq15
    | exact resolve eq15 eq279413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279413
  have eq279484 : (σ (M.op x y)) = (k (σ (τ (σ x))) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq279437
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq279437
    | exact resolve eq279437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279437
  have eq279491 : (σ (M.op x y)) = (k (σ (τ (σ x))) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq279484
    | exact resolve eq279484 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279484
  have eq279494 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq279491
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq279491
    | exact resolve eq279491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279491
  have eq279539 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq269888 eq279494
    | exact resolve eq279494 eq269888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269888 eq279494
  have eq279633 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq279539 eq257418
    | exact resolve eq257418 eq279539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257418 eq279539
  have eq279705 : (σ (M.op x y)) = (σ x) := by grind
  clear eq279633
  have eq279712 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq279705 eq21
    | exact resolve eq21 eq279705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq279713 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq279705 eq29
    | exact resolve eq29 eq279705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq279714 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq279705 eq30
    | exact resolve eq30 eq279705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq279766 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq279705 eq7902
    | exact resolve eq7902 eq279705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902 eq279705
  have eq287828 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq279766
  have eq295656 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq279714 eq153846
    | exact resolve eq153846 eq279714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153846
  have eq295713 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (k (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x)))) := by
    first
    | exact superpose eq279714 eq155111
    | exact resolve eq155111 eq279714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155111
  have eq304888 : (M.op x y) = (k (M.op (k (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x)))) := by
    first
    | exact superpose eq279714 eq295713
    | exact resolve eq295713 eq279714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295713
  have eq311690 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x)))) := by
    first
    | exact superpose eq295656 eq304888
    | exact resolve eq304888 eq295656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295656 eq304888
  have eq311691 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op (k (τ (σ x)) (τ (σ x))) (τ (σ x)))) := by grind
  clear eq311690
  have eq315504 : (M.op x y) = (M.op (M.op x y) (M.op (k (M.op x y) (M.op x y)) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq279714 eq311691
    | exact resolve eq311691 eq279714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279714 eq311691
  have eq317135 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq315504
       have i₂ := eq153767 sF0 sF0
       grind)
    | exact superpose eq153767 eq315504
    | exact resolve eq315504 eq153767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153767 eq315504
  have eq317136 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq317135
  have eq321368 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq279713
       have i₂ := eq153826 sF2 sF3
       grind)
    | exact superpose eq153826 eq279713
    | (have j1 := eq153826 (σ x) (σ y)
       grind)
    | (have r₁ := eq279713
       have r₂ := eq153826 (σ y) (σ x)
       grind)
    | exact resolve eq279713 eq153826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153826
  have eq321371 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq321368
       have r₂ := eq287828
       grind)
    | exact resolve eq321368 eq287828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287828 eq321368
  have eq321470 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq317136 eq15
    | exact resolve eq15 eq317136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317136
  have eq321588 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq279712 eq321470
    | exact resolve eq321470 eq279712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279712 eq321470
  have eq322240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq321588 eq321371
    | exact resolve eq321371 eq321588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321371
  have eq322255 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq322240
       have r₂ := eq279713
       grind)
    | exact resolve eq322240 eq279713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322240
  have eq323051 : (σ x) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq322255 eq153765
    | exact resolve eq153765 eq322255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153765
  have eq323179 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq321588 eq323051
    | exact resolve eq323051 eq321588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323051
  have eq323248 : (σ x) = (σ y) := by
    first
    | exact superpose eq323179 eq322255
    | exact resolve eq322255 eq323179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322255 eq323179
  have eq327450 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq323248 eq279713
    | exact resolve eq279713 eq323248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279713 eq323248
  have eq329718 : (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq327450
       have i₂ := eq96118 sF2
       grind)
    | exact superpose eq96118 eq327450
    | exact resolve eq327450 eq96118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96118 eq327450
  have eq333728 : False := by grind
  exact eq333728

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq469 (σ X0)
       grind)
    | exact superpose eq469 eq15
    | (have j1 := eq469 (σ X0)
       grind)
    | exact resolve eq15 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq525 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq480
  have eq527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq525 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq525
    | (have j0 := eq525 X0
       grind)
    | exact resolve eq525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq528 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq537 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq528 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq528
    | exact resolve eq528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq62
    | exact resolve eq62 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq62
    | exact resolve eq62 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq537 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq537
    | exact resolve eq537 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq569 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq566 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq566
    | exact resolve eq566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq586 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq569 (τ X0)
       grind)
    | exact superpose eq569 eq32
    | exact resolve eq32 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq586 X0
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq586
    | exact resolve eq586 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq657 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq686 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq593 X1
       grind)
    | exact superpose eq593 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq708 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq720 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq528 X1
       grind)
    | exact superpose eq528 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq569 X1
       grind)
    | exact superpose eq569 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq739 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) (τ X0) X1
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq62
    | exact resolve eq62 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq548 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq548 X0 x
       grind)
    | exact superpose eq548 eq548
    | exact resolve eq548 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq814 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq786 X0
       have i₂ := eq569 (k X0 X0)
       grind)
    | exact superpose eq569 eq786
    | exact resolve eq786 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq825 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq814 X0
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq814
    | exact resolve eq814 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq832 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq825 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq825 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq825
    | exact resolve eq825 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq851 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq865 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq851 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq851
    | exact resolve eq851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq873 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq865
  have eq907 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (k X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq549 X0 X1
       grind)
    | exact superpose eq549 eq13
    | (have j0 := eq13 (σ (k X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq916 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k (k X0 X0) (k X0 X0))) ∨ (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq528 (k X0 X0)
       grind)
    | exact superpose eq528 eq907
    | (have j0 := eq907 X0 X1
       grind)
    | exact resolve eq907 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq929 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (k X0 X0) (k X0 X0))) ∨ (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq916 X0 X1
       have i₂ := eq569 (k X0 X0)
       grind)
    | exact superpose eq569 eq916
    | (have j0 := eq916 X0 X1
       grind)
    | exact resolve eq916 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq941 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq929
    | (have j0 := eq929 X0 X1
       grind)
    | exact resolve eq929 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq949 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq941 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq941
    | (have j0 := eq941 X0 X1
       grind)
    | exact resolve eq941 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq950 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq953 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X1
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq950
    | (have j0 := eq950 X0 X1
       grind)
    | exact resolve eq950 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq956 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq959 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq528 (M.op X0 X0)
       grind)
    | exact superpose eq528 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq962 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq569 (M.op X0 X0)
       grind)
    | exact superpose eq569 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq963 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq962 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq962 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq962
    | (have j0 := eq962 X0 X1
       grind)
    | exact resolve eq962 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1114 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ (M.op X0 X0)) (M.op (τ X0) X1)
       have i₂ := eq739 X0 X1
       grind)
    | exact superpose eq739 eq13
    | (have j0 := eq13 (τ (M.op X0 X0)) (M.op (τ X0) X1)
       grind)
    | exact resolve eq13 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq1123 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 X0 X1
       have i₂ := eq593 (M.op X0 X0)
       grind)
    | exact superpose eq593 eq1114
    | (have j0 := eq1114 X0 X1
       grind)
    | exact resolve eq1114 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1133 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1123 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq1123 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq1123
    | (have j0 := eq1123 X0 X1
       grind)
    | exact resolve eq1123 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1134 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1140 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1134 X0 X1
       have i₂ := eq593 (M.op X0 X0)
       grind)
    | exact superpose eq593 eq1134
    | (have j0 := eq1134 X0 X1
       grind)
    | exact resolve eq1134 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1145 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq1140
    | (have j0 := eq1140 X0 X1
       grind)
    | exact resolve eq1140 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq2995 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq722 x y
       grind)
    | exact superpose eq722 eq16
    | (have j1 := eq722 x y
       grind)
    | exact resolve eq16 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3044 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq19049 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq686
    | (have j0 := eq686 X1 (σ X0)
       grind)
    | exact resolve eq686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq19231 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19049 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19049
    | (have j0 := eq19049 X0 X1
       grind)
    | exact resolve eq19049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19049
  have eq19263 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19231 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq19231
    | (have j0 := eq19231 X0 X1
       grind)
    | exact resolve eq19231 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19231
  have eq19285 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19263 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq19263
    | (have j0 := eq19263 X0 X1
       grind)
    | exact resolve eq19263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19263
  have eq19298 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19285 X0 X1
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq19285
    | (have j0 := eq19285 X0 X1
       grind)
    | exact resolve eq19285 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19285
  have eq49396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2995
       have i₂ := eq19298 y x
       grind)
    | exact superpose eq19298 eq2995
    | (have j1 := eq19298 y x
       grind)
    | (have r₁ := eq2995
       have r₂ := eq19298 y x
       grind)
    | exact resolve eq2995 eq19298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995 eq19298
  have eq49397 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq49396
  have eq63410 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3044 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3044
    | (have j0 := eq3044 (τ X0) (τ X1)
       grind)
    | exact resolve eq3044 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63503 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63410 X0 X1
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq63410
    | (have j0 := eq63410 X0 X1
       grind)
    | exact resolve eq63410 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63410
  have eq63561 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63503 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq63503
    | (have j0 := eq63503 X0 X1
       grind)
    | exact resolve eq63503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63503
  have eq63607 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63561 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq63561
    | (have j0 := eq63561 X0 X1
       grind)
    | exact resolve eq63561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63561
  have eq63649 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63607 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq63607
    | (have j0 := eq63607 X0 X1
       grind)
    | exact resolve eq63607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63607
  have eq63686 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63649 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63649
    | (have j0 := eq63649 X0 X1
       grind)
    | exact resolve eq63649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63649
  have eq63713 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63686 X0 X1
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq63686
    | (have j0 := eq63686 X0 X1
       grind)
    | exact resolve eq63686 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63686
  have eq63733 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63713 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq63713
    | (have j0 := eq63713 X0 X1
       grind)
    | exact resolve eq63713 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63713
  have eq63752 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63733 X0 X1
       have i₂ := eq593 X1
       grind)
    | exact superpose eq593 eq63733
    | (have j0 := eq63733 X0 X1
       grind)
    | exact resolve eq63733 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63733
  have eq63767 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63752 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq63752
    | (have j0 := eq63752 X0 X1
       grind)
    | exact resolve eq63752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63752
  have eq63782 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63767 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63767
    | (have j0 := eq63767 X0 X1
       grind)
    | exact resolve eq63767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63767
  have eq71592 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op (σ X0) X1))) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (M.op X0 X0) (M.op (σ X0) X1)
       have i₂ := eq963 X0 X1
       grind)
    | exact superpose eq963 eq29
    | (have j1 := eq963 X0 X1
       grind)
    | exact resolve eq29 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq963
  have eq71691 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71592 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71592
    | (have j0 := eq71592 X0 X1
       grind)
    | exact resolve eq71592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71592
  have eq72392 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) (τ X0)) (τ (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq71691 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71691
    | exact resolve eq71691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71691
  have eq72650 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq72392 X0 X1
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq72392
    | (have j0 := eq72392 X0 X1
       grind)
    | exact resolve eq72392 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72392
  have eq72750 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq72650 X0 X1
       have i₂ := eq32 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact superpose eq32 eq72650
    | (have j0 := eq72650 X0 X1
       grind)
    | exact resolve eq72650 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq72650
  have eq72824 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (σ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72750 X0 X1
       have i₂ := eq593 X0
       grind)
    | exact superpose eq593 eq72750
    | (have j0 := eq72750 X0 X1
       grind)
    | exact resolve eq72750 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq72750
  have eq72880 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72824 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq72824
    | (have j0 := eq72824 X0 X1
       grind)
    | exact resolve eq72824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72824
  have eq73209 : ∀ X0 X1 : G, (τ (M.op X1 X0)) = (τ (k (M.op (M.op X1 X0) (M.op X1 X0)) X0)) ∨ (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72880 (M.op X0 x) (M.op x x)
       have i₂ := eq62 X0 x x
       grind)
    | exact superpose eq62 eq72880
    | exact resolve eq72880 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72880
  have eq80680 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X0 X0) (σ (M.op (τ X0) X1))) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X0) (M.op (τ X0) X1)
       have i₂ := eq1145 X0 X1
       grind)
    | exact superpose eq1145 eq18
    | (have j1 := eq1145 X0 X1
       grind)
    | exact resolve eq18 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1145
  have eq80764 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80680 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80680
    | (have j0 := eq80680 X0 X1
       grind)
    | exact resolve eq80680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80680
  have eq81333 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ (M.op X0 X0))) = (M.op (M.op (τ (σ X0)) X1) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80764 (σ X0) X1
       have i₂ := eq832 X0
       grind)
    | exact superpose eq832 eq80764
    | exact resolve eq80764 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq80764
  have eq81624 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X0) (M.op (τ (σ X0)) X1))) ∨ (τ (σ (M.op X0 X0))) = (M.op (M.op (τ (σ X0)) X1) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81333 X0 X1
       have i₂ := eq15 (M.op X0 X0) (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq15 eq81333
    | (have j0 := eq81333 X0 X1
       grind)
    | exact resolve eq81333 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81333
  have eq81736 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X0) (M.op X0 X1))) ∨ (τ (σ (M.op X0 X0))) = (M.op (M.op (τ (σ X0)) X1) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81624 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81624
    | (have j0 := eq81624 X0 X1
       grind)
    | exact resolve eq81624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81624
  have eq81828 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq81736 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81736
    | (have j0 := eq81736 X0 X1
       grind)
    | exact resolve eq81736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81736
  have eq81894 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X0) (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81828 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq81828
    | (have j0 := eq81828 X0 X1
       grind)
    | exact resolve eq81828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81828
  have eq82181 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (σ (k (M.op (M.op X1 X0) (M.op X1 X0)) X0)) ∨ (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81894 (M.op X0 x) (M.op x x)
       have i₂ := eq62 X0 x x
       grind)
    | exact superpose eq62 eq81894
    | exact resolve eq81894 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81894
  have eq352877 : (σ (M.op x x)) = (σ (k (M.op (M.op x x) (M.op x x)) y)) ∨ (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq82181 y x
       have i₂ := eq49397
       grind)
    | exact superpose eq49397 eq82181
    | exact resolve eq82181 eq49397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49397 eq82181
  have eq352909 : (σ (k x y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq352877
       have i₂ := eq62 x x x
       grind)
    | (have i₁ := eq352877
       have i₂ := eq62 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq62 eq352877
    | exact resolve eq352877 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352877
  have eq352917 : (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3044 x y
       grind)
    | (have r₁ := eq352909
       have r₂ := eq3044 x y
       grind)
    | exact resolve eq352909 eq3044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044 eq352909
  have eq352921 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq352917
       have i₂ := eq62 x x x
       grind)
    | (have i₁ := eq352917
       have i₂ := eq62 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq62 eq352917
    | exact resolve eq352917 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352917
  have eq352922 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq352921
  have eq352924 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352922
       grind)
    | exact superpose eq352922 eq16
    | exact resolve eq16 eq352922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352983 : (τ (σ (M.op x x))) = (τ (k (M.op (σ (M.op x x)) (σ (M.op x x))) (σ y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73209 (σ y) (σ x)
       have i₂ := eq352922
       grind)
    | exact superpose eq352922 eq73209
    | exact resolve eq73209 eq352922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73209 eq352922
  have eq353065 : (τ (σ (M.op x x))) = (k (τ (M.op (σ (M.op x x)) (σ (M.op x x)))) y) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq352983
       have i₂ := eq23 (M.op (σ (M.op x x)) (σ (M.op x x))) y
       grind)
    | exact superpose eq23 eq352983
    | exact resolve eq352983 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq352983
  have eq353117 : (τ (σ (M.op x x))) = (k (τ (σ (k (M.op x x) (M.op x x)))) y) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353065
       have i₂ := eq528 (M.op x x)
       grind)
    | exact superpose eq528 eq353065
    | exact resolve eq353065 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353065
  have eq353166 : (τ (σ (M.op x x))) = (k (k (M.op x x) (M.op x x)) y) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353117
       have i₂ := eq10 (k (M.op x x) (M.op x x))
       grind)
    | exact superpose eq10 eq353117
    | exact resolve eq353117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353117
  have eq353210 : (k (M.op (M.op x x) (M.op x x)) y) = (τ (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353166
       have i₂ := eq569 (M.op x x)
       grind)
    | exact superpose eq569 eq353166
    | exact resolve eq353166 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353166
  have eq353234 : (M.op x x) = (k (M.op (M.op x x) (M.op x x)) y) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353210
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq353210
    | exact resolve eq353210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353210
  have eq353256 : (k x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353234
       have i₂ := eq62 x x x
       grind)
    | (have i₁ := eq353234
       have i₂ := eq62 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq62 eq353234
    | exact resolve eq353234 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353234
  have eq353265 : (σ (k (M.op x x) (M.op x x))) = (M.op (σ y) (σ y)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353256
       have i₂ := eq528 (M.op x x)
       grind)
    | exact superpose eq528 eq353256
    | exact resolve eq353256 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353256
  have eq353269 : (σ (k (M.op x x) (M.op x x))) = (σ (k y y)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353265
       have i₂ := eq528 y
       grind)
    | exact superpose eq528 eq353265
    | exact resolve eq353265 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq353265
  have eq353276 : (σ (M.op y y)) = (σ (k (M.op x x) (M.op x x))) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353269
       have i₂ := eq569 y
       grind)
    | exact superpose eq569 eq353269
    | exact resolve eq353269 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353269
  have eq353277 : (σ (M.op y y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353276
       have i₂ := eq569 (M.op x x)
       grind)
    | exact superpose eq569 eq353276
    | exact resolve eq353276 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq353276
  have eq353278 : (σ x) = (σ (M.op y y)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353277
       have i₂ := eq62 x x x
       grind)
    | (have i₁ := eq353277
       have i₂ := eq62 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq62 eq353277
    | exact resolve eq353277 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq353277
  have eq353279 : (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq353278
  have eq353307 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq63782 x y
       have i₂ := eq353279
       grind)
    | exact superpose eq353279 eq63782
    | (have j0 := eq63782 x y
       grind)
    | (have r₁ := eq63782 x y
       have r₂ := eq353279
       grind)
    | exact resolve eq63782 eq353279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63782 eq353279
  have eq353340 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq353307
  have eq353341 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq353340
  have eq353455 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq352924
       have i₂ := eq353341
       grind)
    | exact superpose eq353341 eq352924
    | exact resolve eq352924 eq353341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352924 eq353341
  have eq353459 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq353455
  have eq353460 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq353459
  have eq353534 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq353460
       grind)
    | exact superpose eq353460 eq10
    | exact resolve eq10 eq353460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353460
  have eq353997 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq353534
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq353534
    | exact resolve eq353534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353534
  have eq353998 : x = (M.op y y) := by grind
  clear eq353997
  have eq354065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq873 y
       have i₂ := eq353998
       grind)
    | exact superpose eq353998 eq873
    | exact resolve eq873 eq353998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq353998
  have eq354456 : False := by grind
  exact eq354456

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq474 (σ X0)
       grind)
    | exact superpose eq474 eq15
    | (have j1 := eq474 (σ X0)
       grind)
    | exact resolve eq15 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq529 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq485
  have eq531 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq529
    | (have j0 := eq529 X0
       grind)
    | exact resolve eq529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq532 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq541 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq532 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq532
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq62
    | exact resolve eq62 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq541 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq541
    | exact resolve eq541 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq541
  have eq574 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq571 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq571
    | exact resolve eq571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq591 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq574 (τ X0)
       grind)
    | exact superpose eq574 eq32
    | exact resolve eq32 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq591 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq591
    | exact resolve eq591 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq670 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
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
  have eq768 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq553 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq553 X0 x
       grind)
    | exact superpose eq553 eq553
    | exact resolve eq553 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq798 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq768 X0
       have i₂ := eq574 (k X0 X0)
       grind)
    | exact superpose eq574 eq768
    | exact resolve eq768 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq810 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq798 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq798
    | exact resolve eq798 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq818 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq810 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq810 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq810
    | exact resolve eq810 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq810
  have eq837 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq818
  have eq854 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq837
    | exact resolve eq837 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq862 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq854
  have eq42948 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq670 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq670
    | exact resolve eq670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq43242 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42948 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq42948
    | (have j0 := eq42948 X0 X1
       grind)
    | exact resolve eq42948 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42948
  have eq43457 : ∀ X0 X1 : G, (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43242 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq43242
    | (have j0 := eq43242 (τ X0) (τ X1)
       grind)
    | exact resolve eq43242 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43242
  have eq43692 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43457 X0 X1
       have i₂ := eq598 X1
       grind)
    | exact superpose eq598 eq43457
    | (have j0 := eq43457 X0 X1
       grind)
    | exact resolve eq43457 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43457
  have eq783574 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq43692 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq43692 X0 X1
       grind)
    | exact superpose eq43692 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq43692 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq43692 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq43692 X0 X1
       grind)
    | exact resolve eq13 eq43692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43692
  have eq783615 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq783574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783574
  have eq783622 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq783615 X0 X1
       have i₂ := eq598 X1
       grind)
    | exact superpose eq598 eq783615
    | (have j0 := eq783615 X0 X1
       grind)
    | exact resolve eq783615 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq783615
  have eq783623 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq783622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783622
  have eq783823 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq783623 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq783623
    | (have j0 := eq783623 X0 X1
       grind)
    | exact resolve eq783623 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783623
  have eq784569 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq783823 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq783823
    | exact resolve eq783823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783823
  have eq785673 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq784569 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq784569
    | (have j0 := eq784569 X0 X1
       grind)
    | exact resolve eq784569 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784569
  have eq786075 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (k X0 (τ X1))) = (τ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq785673 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq785673
    | (have j0 := eq785673 X0 X1
       grind)
    | exact resolve eq785673 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785673
  have eq787654 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = (τ (M.op (σ X0) (τ X1))) ∨ (τ (k (σ X0) (τ X1))) = (τ (M.op (σ X0) (τ X1))) ∨ (σ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (τ X1)
       have i₂ := eq786075 (σ X0) X1
       grind)
    | exact superpose eq786075 eq29
    | (have j1 := eq786075 (σ X0) X1
       grind)
    | exact resolve eq29 eq786075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786075
  have eq788717 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = (τ (M.op (σ X0) (τ X1))) ∨ (k X0 (τ (τ X1))) = (τ (M.op (σ X0) (τ X1))) ∨ (σ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq787654 X0 X1
       have i₂ := eq29 X0 (τ X1)
       grind)
    | exact superpose eq29 eq787654
    | (have j0 := eq787654 X0 X1
       grind)
    | exact resolve eq787654 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq787654
  have eq788718 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = (τ (M.op (σ X0) (τ X1))) ∨ (σ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq788717 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788717
  have eq789730 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq788718 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq788718
    | (have j0 := eq788718 X1 (σ X0)
       grind)
    | exact resolve eq788718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788718
  have eq790877 : ∀ X0 X1 : G, (σ X1) = (τ (σ (k X0 X0))) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq789730 X0 X1
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq789730
    | (have j0 := eq789730 X0 X1
       grind)
    | exact resolve eq789730 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789730
  have eq790971 : ∀ X0 X1 : G, (σ X1) = (k X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq790877 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq790877
    | (have j0 := eq790877 X0 X1
       grind)
    | exact resolve eq790877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790877
  have eq791034 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq790971 X0 X1
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq790971
    | (have j0 := eq790971 X0 X1
       grind)
    | exact resolve eq790971 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790971
  have eq791277 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq791034 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq791034
    | exact resolve eq791034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791034
  have eq792966 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq791277 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq791277
    | (have j0 := eq791277 X0 X1
       grind)
    | exact resolve eq791277 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq791277
  have eq794247 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq792966 X0 X1
       grind)
    | exact superpose eq792966 eq11
    | (have j1 := eq792966 X0 X1
       grind)
    | exact resolve eq11 eq792966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792966
  have eq796156 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq794247 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq794247
    | (have j0 := eq794247 X0 X1
       grind)
    | exact resolve eq794247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794247
  have eq797506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq796156 (σ X0) (σ X1)
       grind)
    | exact superpose eq796156 eq15
    | (have j1 := eq796156 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq796156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797528 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq796156 (τ X0) X1
       grind)
    | exact superpose eq796156 eq18
    | (have j1 := eq796156 (τ X0) X1
       grind)
    | exact resolve eq18 eq796156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq796156
  have eq798890 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq797506 X0 X1
       have i₂ := eq532 X1
       grind)
    | exact superpose eq532 eq797506
    | (have j0 := eq797506 X0 X1
       grind)
    | exact resolve eq797506 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq797506
  have eq799453 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq798890 X0 X1
       have i₂ := eq574 X1
       grind)
    | exact superpose eq574 eq798890
    | (have j0 := eq798890 X0 X1
       grind)
    | exact resolve eq798890 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq798890
  have eq805767 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq797528 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq797528
    | exact resolve eq797528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797528
  have eq806522 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq805767 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq805767
    | (have j0 := eq805767 X0 X1
       grind)
    | exact resolve eq805767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805767
  have eq822009 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq799453 x y
       grind)
    | exact superpose eq799453 eq16
    | (have j1 := eq799453 x y
       grind)
    | exact resolve eq16 eq799453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799453
  have eq824686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq822009
       have i₂ := eq806522 x y
       grind)
    | exact superpose eq806522 eq822009
    | (have j1 := eq806522 x y
       grind)
    | (have r₁ := eq822009
       have r₂ := eq806522 x y
       grind)
    | exact resolve eq822009 eq806522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806522 eq822009
  have eq824689 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq824686
  have eq824708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq862 y
       have i₂ := eq824689
       grind)
    | exact superpose eq824689 eq862
    | exact resolve eq862 eq824689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824689
  have eq825003 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq824708
       have r₂ := eq16
       grind)
    | exact resolve eq824708 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824708
  have eq825079 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq825003
       grind)
    | exact superpose eq825003 eq10
    | exact resolve eq10 eq825003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825003
  have eq825560 : x = (M.op y y) := by
    first
    | (have i₁ := eq825079
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq825079
    | exact resolve eq825079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825079
  have eq825685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq862 y
       have i₂ := eq825560
       grind)
    | exact superpose eq825560 eq862
    | exact resolve eq862 eq825560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq825560
  have eq825980 : False := by grind
  exact eq825980
