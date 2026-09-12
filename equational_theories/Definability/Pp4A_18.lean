import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq63 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
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
  have eq131 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq133 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  clear eq19
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
  have eq550 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 (k X0 X0) X1
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq29
    | (have j1 := eq527 X0
       grind)
    | exact resolve eq29 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq29 (M.op X0 X0) X1
       grind)
    | exact superpose eq29 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
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
  have eq590 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq603 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq941 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq905 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq905
    | (have j0 := eq905 (σ X0)
       grind)
    | exact resolve eq905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq976 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq941 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq941
    | (have j0 := eq941 X0
       grind)
    | exact resolve eq941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq979 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq976 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq976
    | (have j0 := eq976 X0
       grind)
    | exact resolve eq976 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
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
  have eq1191 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq979 X0
       grind)
    | exact superpose eq979 eq435
    | (have j0 := eq435 X0
       have j1 := eq979 X0
       grind)
    | (have r₁ := eq435 X0
       have r₂ := eq979 X0
       grind)
    | exact resolve eq435 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1231 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1191 X0
       have j1 := eq435 X0
       grind)
    | (have r₁ := eq1191 X0
       have r₂ := eq435 X0
       grind)
    | exact resolve eq1191 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
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
  have eq1713 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq1672 (σ X0) X1
       grind)
    | exact superpose eq1672 eq29
    | (have j1 := eq1672 (σ X0) X1
       grind)
    | exact resolve eq29 eq1672
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
  have eq1727 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1713 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1713
    | (have j0 := eq1713 X0 X1
       grind)
    | exact resolve eq1713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1743 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1727 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1727
    | (have j0 := eq1727 X0 X1
       grind)
    | exact resolve eq1727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
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
  clear eq502
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
  have eq3805 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  clear eq1743
  have eq3853 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq4361 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq4430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4361 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4361
    | (have j0 := eq4361 X0 X1
       grind)
    | exact resolve eq4361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq5243 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3853 (M.op X0 X0) (M.op x (σ X0))
       have i₂ := eq3853 X0 x
       grind)
    | exact superpose eq3853 eq3853
    | (have j0 := eq3853 (M.op X0 X0) x
       have j1 := eq3853 (M.op X0 X0) x
       grind)
    | exact resolve eq3853 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5312 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5243 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq5243 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq5243
    | (have j0 := eq5243 X0
       grind)
    | exact resolve eq5243 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243
  have eq5324 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5312 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq5312 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq5312
    | (have j0 := eq5312 X0
       grind)
    | exact resolve eq5312 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312
  have eq5325 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324
  have eq5363 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3853 X0 (σ X0)
       have i₂ := eq5325 X0
       grind)
    | exact superpose eq5325 eq3853
    | (have j0 := eq3853 X0 x
       have j1 := eq5325 X0
       grind)
    | exact resolve eq3853 eq5325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq5401 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5363
  have eq6151 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5401 (k X0 X0)
       have i₂ := eq2059 X0
       grind)
    | exact superpose eq2059 eq5401
    | (have j1 := eq2059 X0
       grind)
    | exact resolve eq5401 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq5401
  have eq6215 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151
  have eq6350 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) X1
       have i₂ := eq6215 X0
       grind)
    | exact superpose eq6215 eq62
    | (have j1 := eq6215 X0
       grind)
    | exact resolve eq62 eq6215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215
  have eq7641 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6350 X0 (σ X0)
       have i₂ := eq5325 X0
       grind)
    | exact superpose eq5325 eq6350
    | (have j0 := eq6350 X0 x
       have j1 := eq5325 X0
       grind)
    | exact resolve eq6350 eq5325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq7686 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7641 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq7641 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq7641 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7641
  have eq8680 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7686 X0
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq7686
    | (have j0 := eq7686 X0
       have j1 := eq527 X0
       grind)
    | exact resolve eq7686 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq7686
  have eq8760 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq8680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8680
  have eq9761 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq8760 X0
       grind)
    | exact superpose eq8760 eq435
    | (have j0 := eq435 X0
       have j1 := eq8760 X0
       grind)
    | exact resolve eq435 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq8760
  have eq9817 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9761
  have eq11847 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k (k X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq560
    | (have j0 := eq560 X1 X1
       grind)
    | exact resolve eq560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq11901 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X1
       have i₂ := eq11847 X0 X1
       grind)
    | exact superpose eq11847 eq2229
    | (have j0 := eq2229 X0
       have j1 := eq11847 X1 X0
       grind)
    | exact resolve eq2229 eq11847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq11847
  have eq11951 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11901 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq12052 : ∀ X0 : G, (k (M.op X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2481 X0
       have i₂ := eq11951 X0 (k X0 X0)
       grind)
    | exact superpose eq11951 eq2481
    | (have j0 := eq2481 X0
       have j1 := eq11951 X0 x
       grind)
    | exact resolve eq2481 eq11951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq11951
  have eq12158 : ∀ X0 : G, (k (M.op X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12052 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq12052 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq12052 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq12052
  have eq12311 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12158 (M.op X0 X0)
       have i₂ := eq2542 X0
       grind)
    | exact superpose eq2542 eq12158
    | (have j1 := eq2542 X0
       grind)
    | exact resolve eq12158 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq12158
  have eq12324 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12311 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311
  have eq12328 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq12324 X0
       have j1 := eq94 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12324 x
       have r₂ := eq94 x x x
       grind)
    | exact resolve eq12324 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq12324
  have eq12362 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12328 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq12328 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq12328
    | exact resolve eq12328 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12328
  have eq12531 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12362 (σ X0)
       grind)
    | exact superpose eq12362 eq15
    | exact resolve eq15 eq12362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12561 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12531 X0
       have i₂ := eq12362 X0
       grind)
    | exact superpose eq12362 eq12531
    | exact resolve eq12531 eq12362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12362 eq12531
  have eq20001 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq20024 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20001 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq20001
    | (have j0 := eq20001 X0 X1
       grind)
    | exact resolve eq20001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20001
  have eq20032 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20024 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20024
    | (have j0 := eq20024 X0 X1
       grind)
    | exact resolve eq20024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq20035 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20032 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20032
    | (have j0 := eq20032 X0 X1
       grind)
    | exact resolve eq20032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20032
  have eq20037 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20035 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20035
    | (have j0 := eq20035 X0 X1
       grind)
    | exact resolve eq20035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20035
  have eq20039 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20037 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20037
    | (have j0 := eq20037 X0 X1
       grind)
    | exact resolve eq20037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20037
  have eq20041 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20039 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20039
    | (have j0 := eq20039 X0 X1
       grind)
    | exact resolve eq20039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20039
  have eq49829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq590
       have i₂ := eq4430 y x
       grind)
    | exact superpose eq4430 eq590
    | (have j1 := eq4430 (σ x) (σ y)
       grind)
    | (have r₁ := eq590
       have r₂ := eq4430 y x
       grind)
    | (have r₁ := eq590
       have r₂ := eq4430 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq590
       have r₂ := eq4430 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq590 eq4430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4430
  have eq49830 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq49829
  have eq227032 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49830
       grind)
    | exact superpose eq49830 eq16
    | exact resolve eq16 eq49830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49830
  have eq227033 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq227032
       have r₂ := eq12561 x
       grind)
    | exact resolve eq227032 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227032
  have eq227036 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq227033
       grind)
    | exact superpose eq227033 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq227033
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq227033
       grind)
    | exact resolve eq12 eq227033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227037 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 x y
       have i₂ := eq227033
       grind)
    | exact superpose eq227033 eq62
    | exact resolve eq62 eq227033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227033
  have eq227079 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq227036
  have eq227098 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq227037 (M.op x x)
       have i₂ := eq227037 x
       grind)
    | exact superpose eq227037 eq227037
    | exact resolve eq227037 eq227037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227037
  have eq227163 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq227098
  have eq227229 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (σ x) (σ y)
       have i₂ := eq227163
       grind)
    | exact superpose eq227163 eq62
    | exact resolve eq62 eq227163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq227163
  have eq238822 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq227079
       grind)
    | exact superpose eq227079 eq603
    | (have j0 := eq603 x y
       grind)
    | exact resolve eq603 eq227079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq227079
  have eq238839 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq238822
  have eq238926 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq227229 (M.op x (σ x))
       have i₂ := eq227229 x
       grind)
    | exact superpose eq227229 eq227229
    | exact resolve eq227229 eq227229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227229
  have eq239015 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq238926
  have eq239046 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq239015
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq239015
    | exact resolve eq239015 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239015
  have eq239074 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq239046
       grind)
    | exact superpose eq239046 eq10
    | exact resolve eq10 eq239046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239046
  have eq239314 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq239074
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq239074
    | exact resolve eq239074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239074
  have eq239402 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239314
       grind)
    | exact superpose eq239314 eq16
    | exact resolve eq16 eq239314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239314
  have eq239432 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j1 := eq5325 x
       grind)
    | (have r₁ := eq239402
       have r₂ := eq5325 x
       grind)
    | exact resolve eq239402 eq5325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5325 eq239402
  have eq239433 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq238839
       have i₂ := eq239432
       grind)
    | exact superpose eq239432 eq238839
    | (have r₁ := eq238839
       have r₂ := eq239432
       grind)
    | exact resolve eq238839 eq239432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239476 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9817 x
       have i₂ := eq239432
       grind)
    | exact superpose eq239432 eq9817
    | (have j0 := eq9817 x
       grind)
    | exact resolve eq9817 eq239432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817 eq239432
  have eq239562 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq239476
  have eq239573 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq239433
  have eq239602 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1231 x
       grind)
    | (have r₁ := eq239562
       have r₂ := eq1231 x
       grind)
    | exact resolve eq239562 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq239562
  have eq239629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq239573
       have r₂ := eq238839
       grind)
    | exact resolve eq239573 eq238839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238839 eq239573
  have eq239645 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq239602
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq239602
    | exact resolve eq239602 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239602
  have eq245662 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239629
       grind)
    | exact superpose eq239629 eq16
    | exact resolve eq16 eq239629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245710 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq239629
       grind)
    | exact superpose eq239629 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq239629
       grind)
    | exact resolve eq12 eq239629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239629
  have eq245756 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq245710
  have eq245776 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq245756
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq245756
    | exact resolve eq245756 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245756
  have eq245817 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq245776
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq245776
    | exact resolve eq245776 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245776
  have eq245834 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq245817
       have i₂ := eq239645
       grind)
    | exact superpose eq239645 eq245817
    | exact resolve eq245817 eq239645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245817
  have eq245849 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq245834
       grind)
    | exact superpose eq245834 eq10
    | exact resolve eq10 eq245834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245834
  have eq246073 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq245849
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq245849
    | exact resolve eq245849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245849
  have eq246761 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq246073
       grind)
    | exact superpose eq246073 eq16
    | exact resolve eq16 eq246073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246073
  have eq246798 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq246761
       have r₂ := eq12561 x
       grind)
    | exact resolve eq246761 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246761
  have eq246828 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq246798
       grind)
    | exact superpose eq246798 eq10
    | exact resolve eq10 eq246798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246798
  have eq247055 : x = (k y x) := by
    first
    | (have i₁ := eq246828
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq246828
    | exact resolve eq246828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246828
  have eq247148 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20041 y x
       have i₂ := eq247055
       grind)
    | exact superpose eq247055 eq20041
    | (have j0 := eq20041 x y
       grind)
    | (have r₁ := eq20041 y x
       have r₂ := eq247055
       grind)
    | exact resolve eq20041 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20041 eq247055
  have eq247160 : x = y ∨ x = (M.op x y) := by grind
  clear eq247148
  have eq247179 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247160
       grind)
    | exact superpose eq247160 eq16
    | exact resolve eq16 eq247160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247160
  have eq247220 : x = (M.op x y) := by
    first
    | (have r₁ := eq247179
       have r₂ := eq12561 x
       grind)
    | exact resolve eq247179 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247179
  have eq247231 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq245662
       have i₂ := eq247220
       grind)
    | exact superpose eq247220 eq245662
    | exact resolve eq245662 eq247220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245662
  have eq247295 : (σ x) = (σ y) := by grind
  clear eq247231
  have eq247324 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247295
       grind)
    | exact superpose eq247295 eq16
    | exact resolve eq16 eq247295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247295
  have eq247551 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq247324
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq247324
    | exact resolve eq247324 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12561 eq247324
  have eq247573 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq247551
       have i₂ := eq239645
       grind)
    | exact superpose eq239645 eq247551
    | exact resolve eq247551 eq239645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239645 eq247551
  have eq247585 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq247573
       have i₂ := eq247220
       grind)
    | exact superpose eq247220 eq247573
    | exact resolve eq247573 eq247220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247220 eq247573
  have eq247586 : False := by grind
  exact eq247586

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq63 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op (M.op X0 X1) X2) X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
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
  have eq131 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq133 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  clear eq19
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
  have eq550 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 (k X0 X0) X1
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq29
    | (have j1 := eq527 X0
       grind)
    | exact resolve eq29 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq29 (M.op X0 X0) X1
       grind)
    | exact superpose eq29 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
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
  have eq590 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq603 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq941 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq905 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq905
    | (have j0 := eq905 (σ X0)
       grind)
    | exact resolve eq905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq976 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq941 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq941
    | (have j0 := eq941 X0
       grind)
    | exact resolve eq941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq979 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq976 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq976
    | (have j0 := eq976 X0
       grind)
    | exact resolve eq976 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
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
  have eq1191 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq979 X0
       grind)
    | exact superpose eq979 eq435
    | (have j0 := eq435 X0
       have j1 := eq979 X0
       grind)
    | (have r₁ := eq435 X0
       have r₂ := eq979 X0
       grind)
    | exact resolve eq435 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1231 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1191 X0
       have j1 := eq435 X0
       grind)
    | (have r₁ := eq1191 X0
       have r₂ := eq435 X0
       grind)
    | exact resolve eq1191 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
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
  have eq1713 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq1672 (σ X0) X1
       grind)
    | exact superpose eq1672 eq29
    | (have j1 := eq1672 (σ X0) X1
       grind)
    | exact resolve eq29 eq1672
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
  have eq1727 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1713 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1713
    | (have j0 := eq1713 X0 X1
       grind)
    | exact resolve eq1713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1743 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1727 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1727
    | (have j0 := eq1727 X0 X1
       grind)
    | exact resolve eq1727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
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
  clear eq502
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
  have eq3805 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  clear eq1743
  have eq3853 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq4361 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq4430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4361 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4361
    | (have j0 := eq4361 X0 X1
       grind)
    | exact resolve eq4361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq5243 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3853 (M.op X0 X0) (M.op x (σ X0))
       have i₂ := eq3853 X0 x
       grind)
    | exact superpose eq3853 eq3853
    | (have j0 := eq3853 (M.op X0 X0) x
       have j1 := eq3853 (M.op X0 X0) x
       grind)
    | exact resolve eq3853 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5312 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5243 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq5243 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq5243
    | (have j0 := eq5243 X0
       grind)
    | exact resolve eq5243 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243
  have eq5324 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5312 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq5312 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq5312
    | (have j0 := eq5312 X0
       grind)
    | exact resolve eq5312 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312
  have eq5325 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324
  have eq5363 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3853 X0 (σ X0)
       have i₂ := eq5325 X0
       grind)
    | exact superpose eq5325 eq3853
    | (have j0 := eq3853 X0 x
       have j1 := eq5325 X0
       grind)
    | exact resolve eq3853 eq5325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq5401 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5363
  have eq6151 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5401 (k X0 X0)
       have i₂ := eq2059 X0
       grind)
    | exact superpose eq2059 eq5401
    | (have j1 := eq2059 X0
       grind)
    | exact resolve eq5401 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq5401
  have eq6215 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151
  have eq6350 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) X1
       have i₂ := eq6215 X0
       grind)
    | exact superpose eq6215 eq62
    | (have j1 := eq6215 X0
       grind)
    | exact resolve eq62 eq6215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215
  have eq7641 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6350 X0 (σ X0)
       have i₂ := eq5325 X0
       grind)
    | exact superpose eq5325 eq6350
    | (have j0 := eq6350 X0 x
       have j1 := eq5325 X0
       grind)
    | exact resolve eq6350 eq5325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350
  have eq7686 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7641 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq7641 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq7641 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7641
  have eq8680 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7686 X0
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq7686
    | (have j0 := eq7686 X0
       have j1 := eq527 X0
       grind)
    | exact resolve eq7686 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq7686
  have eq8760 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq8680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8680
  have eq9761 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq8760 X0
       grind)
    | exact superpose eq8760 eq435
    | (have j0 := eq435 X0
       have j1 := eq8760 X0
       grind)
    | exact resolve eq435 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq8760
  have eq9817 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9761
  have eq11847 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k (k X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq560
    | (have j0 := eq560 X1 X1
       grind)
    | exact resolve eq560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq11901 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (k X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X1
       have i₂ := eq11847 X0 X1
       grind)
    | exact superpose eq11847 eq2229
    | (have j0 := eq2229 X0
       have j1 := eq11847 X1 X0
       grind)
    | exact resolve eq2229 eq11847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq11847
  have eq11951 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11901 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq12052 : ∀ X0 : G, (k (M.op X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2481 X0
       have i₂ := eq11951 X0 (k X0 X0)
       grind)
    | exact superpose eq11951 eq2481
    | (have j0 := eq2481 X0
       have j1 := eq11951 X0 x
       grind)
    | exact resolve eq2481 eq11951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq11951
  have eq12158 : ∀ X0 : G, (k (M.op X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12052 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq12052 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq12052 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq12052
  have eq12311 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12158 (M.op X0 X0)
       have i₂ := eq2542 X0
       grind)
    | exact superpose eq2542 eq12158
    | (have j1 := eq2542 X0
       grind)
    | exact resolve eq12158 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq12158
  have eq12324 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12311 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311
  have eq12328 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq12324 X0
       have j1 := eq94 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12324 x
       have r₂ := eq94 x x x
       grind)
    | exact resolve eq12324 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq12324
  have eq12362 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12328 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq12328 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq12328
    | exact resolve eq12328 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12328
  have eq12531 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12362 (σ X0)
       grind)
    | exact superpose eq12362 eq15
    | exact resolve eq15 eq12362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12561 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12531 X0
       have i₂ := eq12362 X0
       grind)
    | exact superpose eq12362 eq12531
    | exact resolve eq12531 eq12362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12362 eq12531
  have eq20001 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq20024 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20001 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq20001
    | (have j0 := eq20001 X0 X1
       grind)
    | exact resolve eq20001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20001
  have eq20032 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20024 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20024
    | (have j0 := eq20024 X0 X1
       grind)
    | exact resolve eq20024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq20035 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20032 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20032
    | (have j0 := eq20032 X0 X1
       grind)
    | exact resolve eq20032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20032
  have eq20037 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20035 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20035
    | (have j0 := eq20035 X0 X1
       grind)
    | exact resolve eq20035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20035
  have eq20039 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20037 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20037
    | (have j0 := eq20037 X0 X1
       grind)
    | exact resolve eq20037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20037
  have eq20041 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20039 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20039
    | (have j0 := eq20039 X0 X1
       grind)
    | exact resolve eq20039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20039
  have eq49829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq590
       have i₂ := eq4430 y x
       grind)
    | exact superpose eq4430 eq590
    | (have j1 := eq4430 (σ x) (σ y)
       grind)
    | (have r₁ := eq590
       have r₂ := eq4430 y x
       grind)
    | (have r₁ := eq590
       have r₂ := eq4430 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq590
       have r₂ := eq4430 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq590 eq4430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4430
  have eq49830 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq49829
  have eq227032 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49830
       grind)
    | exact superpose eq49830 eq16
    | exact resolve eq16 eq49830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49830
  have eq227033 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq227032
       have r₂ := eq12561 x
       grind)
    | exact resolve eq227032 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227032
  have eq227036 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq227033
       grind)
    | exact superpose eq227033 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq227033
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq227033
       grind)
    | exact resolve eq12 eq227033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227037 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 x y
       have i₂ := eq227033
       grind)
    | exact superpose eq227033 eq62
    | exact resolve eq62 eq227033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227033
  have eq227079 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq227036
  have eq227098 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq227037 (M.op x x)
       have i₂ := eq227037 x
       grind)
    | exact superpose eq227037 eq227037
    | exact resolve eq227037 eq227037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227037
  have eq227163 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq227098
  have eq227229 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (σ x) (σ y)
       have i₂ := eq227163
       grind)
    | exact superpose eq227163 eq62
    | exact resolve eq62 eq227163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq227163
  have eq238822 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq227079
       grind)
    | exact superpose eq227079 eq603
    | (have j0 := eq603 x y
       grind)
    | exact resolve eq603 eq227079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq227079
  have eq238839 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq238822
  have eq238926 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq227229 (M.op x (σ x))
       have i₂ := eq227229 x
       grind)
    | exact superpose eq227229 eq227229
    | exact resolve eq227229 eq227229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227229
  have eq239015 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq238926
  have eq239046 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq239015
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq239015
    | exact resolve eq239015 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239015
  have eq239074 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq239046
       grind)
    | exact superpose eq239046 eq10
    | exact resolve eq10 eq239046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239046
  have eq239314 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq239074
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq239074
    | exact resolve eq239074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239074
  have eq239402 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239314
       grind)
    | exact superpose eq239314 eq16
    | exact resolve eq16 eq239314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239314
  have eq239432 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have j1 := eq5325 x
       grind)
    | (have r₁ := eq239402
       have r₂ := eq5325 x
       grind)
    | exact resolve eq239402 eq5325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5325 eq239402
  have eq239433 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq238839
       have i₂ := eq239432
       grind)
    | exact superpose eq239432 eq238839
    | (have r₁ := eq238839
       have r₂ := eq239432
       grind)
    | exact resolve eq238839 eq239432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239476 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9817 x
       have i₂ := eq239432
       grind)
    | exact superpose eq239432 eq9817
    | (have j0 := eq9817 x
       grind)
    | exact resolve eq9817 eq239432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817 eq239432
  have eq239562 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq239476
  have eq239573 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq239433
  have eq239602 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1231 x
       grind)
    | (have r₁ := eq239562
       have r₂ := eq1231 x
       grind)
    | exact resolve eq239562 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq239562
  have eq239629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq239573
       have r₂ := eq238839
       grind)
    | exact resolve eq239573 eq238839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238839 eq239573
  have eq239645 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq239602
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq239602
    | exact resolve eq239602 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239602
  have eq245662 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239629
       grind)
    | exact superpose eq239629 eq16
    | exact resolve eq16 eq239629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245710 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq239629
       grind)
    | exact superpose eq239629 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq239629
       grind)
    | exact resolve eq12 eq239629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239629
  have eq245756 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq245710
  have eq245776 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq245756
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq245756
    | exact resolve eq245756 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245756
  have eq245817 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq245776
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq245776
    | exact resolve eq245776 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245776
  have eq245834 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq245817
       have i₂ := eq239645
       grind)
    | exact superpose eq239645 eq245817
    | exact resolve eq245817 eq239645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245817
  have eq245849 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq245834
       grind)
    | exact superpose eq245834 eq10
    | exact resolve eq10 eq245834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245834
  have eq246073 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq245849
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq245849
    | exact resolve eq245849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245849
  have eq246761 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq246073
       grind)
    | exact superpose eq246073 eq16
    | exact resolve eq16 eq246073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246073
  have eq246798 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq246761
       have r₂ := eq12561 x
       grind)
    | exact resolve eq246761 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246761
  have eq246828 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq246798
       grind)
    | exact superpose eq246798 eq10
    | exact resolve eq10 eq246798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246798
  have eq247055 : x = (k y x) := by
    first
    | (have i₁ := eq246828
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq246828
    | exact resolve eq246828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246828
  have eq247148 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20041 y x
       have i₂ := eq247055
       grind)
    | exact superpose eq247055 eq20041
    | (have j0 := eq20041 x y
       grind)
    | (have r₁ := eq20041 y x
       have r₂ := eq247055
       grind)
    | exact resolve eq20041 eq247055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20041 eq247055
  have eq247160 : x = y ∨ x = (M.op x y) := by grind
  clear eq247148
  have eq247179 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247160
       grind)
    | exact superpose eq247160 eq16
    | exact resolve eq16 eq247160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247160
  have eq247220 : x = (M.op x y) := by
    first
    | (have r₁ := eq247179
       have r₂ := eq12561 x
       grind)
    | exact resolve eq247179 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247179
  have eq247231 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq245662
       have i₂ := eq247220
       grind)
    | exact superpose eq247220 eq245662
    | exact resolve eq245662 eq247220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245662
  have eq247295 : (σ x) = (σ y) := by grind
  clear eq247231
  have eq247324 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247295
       grind)
    | exact superpose eq247295 eq16
    | exact resolve eq16 eq247295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247295
  have eq247551 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq247324
       have i₂ := eq12561 x
       grind)
    | exact superpose eq12561 eq247324
    | exact resolve eq247324 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12561 eq247324
  have eq247573 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq247551
       have i₂ := eq239645
       grind)
    | exact superpose eq239645 eq247551
    | exact resolve eq247551 eq239645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239645 eq247551
  have eq247585 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq247573
       have i₂ := eq247220
       grind)
    | exact superpose eq247220 eq247573
    | exact resolve eq247573 eq247220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247220 eq247573
  have eq247586 : False := by grind
  exact eq247586

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq73 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq468 (σ X0)
       grind)
    | exact superpose eq468 eq15
    | (have j1 := eq468 (σ X0)
       grind)
    | exact resolve eq15 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq468 (τ X0)
       grind)
    | exact superpose eq468 eq18
    | (have j1 := eq468 (τ X0)
       grind)
    | exact resolve eq18 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq468
  have eq491 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq486 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq486
    | (have j0 := eq486 X0
       grind)
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq528 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq479
  have eq565 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq563 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 X0
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq566 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq575 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq566 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq566
    | exact resolve eq566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq62
    | exact resolve eq62 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) X1
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq62
    | exact resolve eq62 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq73 (σ X0)
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq73
    | exact resolve eq73 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq597 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq597
    | exact resolve eq597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq606 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq575 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq575
    | exact resolve eq575 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq609 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq606 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq606
    | exact resolve eq606 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq628 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq609 (τ X0)
       grind)
    | exact superpose eq609 eq32
    | exact resolve eq32 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq628 X0
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq628
    | exact resolve eq628 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq752 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq585 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq585 X0 x
       grind)
    | exact superpose eq585 eq585
    | exact resolve eq585 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq779 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq752 X0
       have i₂ := eq609 (k X0 X0)
       grind)
    | exact superpose eq609 eq752
    | exact resolve eq752 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq789 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq779 X0
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq779
    | exact resolve eq779 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq795 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq789 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq789 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq789
    | exact resolve eq789 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq815 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq826 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq815 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq815
    | exact resolve eq815 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq835 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq826
  have eq1416 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq586 X0 (σ (k X0 X0))
       have i₂ := eq600 X0
       grind)
    | exact superpose eq600 eq586
    | exact resolve eq586 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq600
  have eq1441 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (k X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1416 X0
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq1416
    | exact resolve eq1416 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1465 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1441 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1441
    | exact resolve eq1441 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1441
  have eq2662 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 (σ X0) (σ X1)
       have i₂ := eq528 X0 X1
       grind)
    | exact superpose eq528 eq62
    | (have j1 := eq528 X0 X1
       grind)
    | exact resolve eq62 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2663 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) (σ X1) X2
       have i₂ := eq528 X0 X1
       grind)
    | exact superpose eq528 eq62
    | (have j1 := eq528 X0 X1
       grind)
    | exact resolve eq62 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq2674 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2663 X0 X1 X2
       have i₂ := eq566 X1
       grind)
    | exact superpose eq566 eq2663
    | (have j0 := eq2663 X0 X1 X2
       grind)
    | exact resolve eq2663 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2675 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2662 X0 X1 X2
       have i₂ := eq566 X1
       grind)
    | exact superpose eq566 eq2662
    | (have j0 := eq2662 X0 X1 X2
       grind)
    | exact resolve eq2662 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2705 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2674 X0 X1 X2
       have i₂ := eq609 X1
       grind)
    | exact superpose eq609 eq2674
    | (have j0 := eq2674 X0 X1 X2
       grind)
    | exact resolve eq2674 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq2706 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2675 X0 X1 X2
       have i₂ := eq609 X1
       grind)
    | exact superpose eq609 eq2675
    | (have j0 := eq2675 X0 X1 X2
       grind)
    | exact resolve eq2675 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675
  have eq2734 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2705 X0 X1 X2
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq2705
    | (have j0 := eq2705 X0 X1 X2
       grind)
    | exact resolve eq2705 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2735 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2706 X0 X1 X2
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq2706
    | (have j0 := eq2706 X0 X1 X2
       grind)
    | exact resolve eq2706 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706
  have eq2763 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2734 X0 X1 X2
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq2734
    | (have j0 := eq2734 X0 X1 X2
       grind)
    | exact resolve eq2734 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2764 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2735 X0 X1 X2
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq2735
    | (have j0 := eq2735 X0 X1 X2
       grind)
    | exact resolve eq2735 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2792 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2763 X0 X1 X2
       have i₂ := eq566 X1
       grind)
    | exact superpose eq566 eq2763
    | (have j0 := eq2763 X0 X1 X2
       grind)
    | exact resolve eq2763 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2793 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2764 X0 X1 X2
       have i₂ := eq566 X1
       grind)
    | exact superpose eq566 eq2764
    | (have j0 := eq2764 X0 X1 X2
       grind)
    | exact resolve eq2764 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764
  have eq2821 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2792 X0 X1 X2
       have i₂ := eq609 X1
       grind)
    | exact superpose eq609 eq2792
    | (have j0 := eq2792 X0 X1 X2
       grind)
    | exact resolve eq2792 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792
  have eq2822 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2793 X0 X1 X2
       have i₂ := eq609 X1
       grind)
    | exact superpose eq609 eq2793
    | (have j0 := eq2793 X0 X1 X2
       grind)
    | exact resolve eq2793 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793
  have eq34291 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2821 (τ X0) (τ X1) X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2821
    | (have j0 := eq2821 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq2821 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821
  have eq34498 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X1 X2)) = X1 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34291 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34291
    | (have j0 := eq34291 X0 X1 X2
       grind)
    | exact resolve eq34291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34291
  have eq34587 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34498 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq34498
    | (have j0 := eq34498 X0 X1 X2
       grind)
    | exact resolve eq34498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34498
  have eq34655 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (σ (τ (M.op X1 X1))) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34587 X0 X1 X2
       have i₂ := eq635 X1
       grind)
    | exact superpose eq635 eq34587
    | (have j0 := eq34587 X0 X1 X2
       grind)
    | exact resolve eq34587 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34587
  have eq34720 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34655 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq34655
    | (have j0 := eq34655 X0 X1 X2
       grind)
    | exact resolve eq34655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34655
  have eq34767 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34720 X0 X1 X2
       have i₂ := eq635 X0
       grind)
    | exact superpose eq635 eq34720
    | (have j0 := eq34720 X0 X1 X2
       grind)
    | exact resolve eq34720 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34720
  have eq34807 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34767 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq34767
    | (have j0 := eq34767 X0 X1 X2
       grind)
    | exact resolve eq34767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34767
  have eq34831 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34807 X0 X1 X2
       have i₂ := eq635 X1
       grind)
    | exact superpose eq635 eq34807
    | (have j0 := eq34807 X0 X1 X2
       grind)
    | exact resolve eq34807 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34807
  have eq34854 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34831 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq34831
    | (have j0 := eq34831 X0 X1 X2
       grind)
    | exact resolve eq34831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34831
  have eq34873 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34854 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34854
    | (have j0 := eq34854 X0 X1 X2
       grind)
    | exact resolve eq34854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34854
  have eq35013 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) ∨ (M.op X1 X1) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34873 X1 (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq1465 X0
       grind)
    | exact superpose eq1465 eq34873
    | (have j0 := eq34873 (σ (M.op X0 X0)) X1 x
       grind)
    | exact resolve eq34873 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq34873
  have eq35165 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35013 X0 X1
       have i₂ := eq566 (M.op X0 X0)
       grind)
    | exact superpose eq566 eq35013
    | (have j0 := eq35013 X0 X1
       grind)
    | exact resolve eq35013 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35013
  have eq35275 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35165 X0 X1
       have i₂ := eq609 (M.op X0 X0)
       grind)
    | exact superpose eq609 eq35165
    | (have j0 := eq35165 X0 X1
       grind)
    | exact resolve eq35165 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35165
  have eq35378 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35275 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq35275 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq35275
    | (have j0 := eq35275 X0 X1
       grind)
    | exact resolve eq35275 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35275
  have eq35473 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) (M.op X0 X0))) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35378 X0 X1
       have i₂ := eq566 (M.op X0 X0)
       grind)
    | exact superpose eq566 eq35378
    | (have j0 := eq35378 X0 X1
       grind)
    | exact resolve eq35378 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35378
  have eq35546 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35473 X0 X1
       have i₂ := eq609 (M.op X0 X0)
       grind)
    | exact superpose eq609 eq35473
    | (have j0 := eq35473 X0 X1
       grind)
    | exact resolve eq35473 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35473
  have eq35601 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (k X1 (σ (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35546 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq35546 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq35546
    | (have j0 := eq35546 X0 X1
       grind)
    | exact resolve eq35546 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35546
  have eq43445 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (k (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2822 X0 (τ X1) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq2822
    | (have j0 := eq2822 X0 (τ X1) X2
       grind)
    | exact resolve eq2822 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq43499 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (τ (M.op X1 X1))) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (k (σ X0) X1)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43445 X0 X1 X2
       have i₂ := eq635 X1
       grind)
    | exact superpose eq635 eq43445
    | (have j0 := eq43445 X0 X1 X2
       grind)
    | exact resolve eq43445 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43445
  have eq43606 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (k (σ X0) X1)) ∨ (σ X0) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43499 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq43499
    | (have j0 := eq43499 X0 X1 X2
       grind)
    | exact resolve eq43499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43499
  have eq43687 : ∀ X0 X1 X2 : G, (σ X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43606 X0 X1 X2
       have i₂ := eq635 X1
       grind)
    | exact superpose eq635 eq43606
    | (have j0 := eq43606 X0 X1 X2
       grind)
    | exact resolve eq43606 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43606
  have eq43751 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (k (σ X0) X1)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43687 X0 X1 X2
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq43687
    | (have j0 := eq43687 X0 X1 X2
       grind)
    | exact resolve eq43687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43687
  have eq48047 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (k X1 (σ (M.op (τ X0) (τ X0)))) X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35601 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35601
    | (have j0 := eq35601 (M.op (τ X0) (τ X0)) (M.op (k X1 (σ (M.op (τ X0) (τ X0)))) X0)
       grind)
    | exact resolve eq35601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35601
  have eq48163 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op (k X1 (σ (τ (M.op X0 X0)))) X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48047 X0 X1
       have i₂ := eq635 X0
       grind)
    | exact superpose eq635 eq48047
    | (have j0 := eq48047 X0 X1
       grind)
    | exact resolve eq48047 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48047
  have eq48200 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X1 (M.op X0 X0)) X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48163 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq48163
    | (have j0 := eq48163 X0 X1
       grind)
    | exact resolve eq48163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48163
  have eq48322 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X0)) = (M.op (M.op X1 (k X2 (M.op X0 X0))) (M.op X0 X0)) ∨ (M.op X2 X2) = X0 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (k X2 (M.op X0 X0)) X0
       have i₂ := eq48200 X0 X2
       grind)
    | exact superpose eq48200 eq62
    | (have j1 := eq48200 X0 X2
       grind)
    | exact resolve eq62 eq48200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48200
  have eq80332 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48322 X1 (M.op x (σ X0)) (σ X0)
       have i₂ := eq43751 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq43751 eq48322
    | (have j0 := eq48322 X1 X1 (σ X0)
       have j1 := eq43751 X0 (M.op X1 X1) x
       grind)
    | exact resolve eq48322 eq43751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43751 eq48322
  have eq80362 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80332 X0 X1
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq80332
    | (have j0 := eq80332 X0 X1
       grind)
    | exact resolve eq80332 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80332
  have eq80454 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80362 X0 X1
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq80362
    | (have j0 := eq80362 X0 X1
       grind)
    | exact resolve eq80362 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80362
  have eq80518 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ X0) = X1 ∨ (σ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80454 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq80454 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq80454
    | (have j0 := eq80454 X0 X1
       grind)
    | exact resolve eq80454 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80454
  have eq80519 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ X0) = X1 ∨ (σ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80518 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80518
  have eq80563 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80519 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq80519 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq80519
    | (have j0 := eq80519 X0 X1
       grind)
    | exact resolve eq80519 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80519
  have eq80564 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 X1)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = X1 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80563
  have eq80638 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80564 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80564
    | (have j0 := eq80564 (τ X0) X1
       grind)
    | exact resolve eq80564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80564
  have eq80759 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X0 (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80638 X0 X1
       have i₂ := eq635 X0
       grind)
    | exact superpose eq635 eq80638
    | (have j0 := eq80638 X0 X1
       grind)
    | exact resolve eq80638 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80638
  have eq80775 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80759 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq80759
    | (have j0 := eq80759 X0 X1
       grind)
    | exact resolve eq80759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80759
  have eq80812 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = (k X1 (τ (M.op X0 X0))) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80775 X0 (τ X0)
       have i₂ := eq635 X0
       grind)
    | exact superpose eq635 eq80775
    | (have j0 := eq80775 X1 (τ X0)
       grind)
    | exact resolve eq80775 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80775
  have eq82067 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80812 (M.op x x) X1
       have i₂ := eq62 x x x
       grind)
    | exact superpose eq62 eq80812
    | (have j0 := eq80812 (M.op X0 X0) X1
       grind)
    | exact resolve eq80812 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80812
  have eq83009 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq82067 X1 (τ X0)
       grind)
    | exact superpose eq82067 eq32
    | (have j1 := eq82067 X1 (τ X0)
       grind)
    | exact resolve eq32 eq82067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq82067
  have eq83075 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83009 X0 X1
       have i₂ := eq635 X0
       grind)
    | exact superpose eq635 eq83009
    | (have j0 := eq83009 X0 X1
       grind)
    | exact resolve eq83009 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83009
  have eq154220 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 (M.op X0 X0)
       have i₂ := eq83075 X0 X1
       grind)
    | (have i₁ := eq491 (M.op X1 X1)
       have i₂ := eq83075 X0 X1
       grind)
    | exact superpose eq83075 eq491
    | (have j0 := eq491 (M.op X0 X0)
       have j1 := eq83075 X0 X1
       grind)
    | exact resolve eq491 eq83075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq154223 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (τ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq635 (M.op X0 X0)
       have i₂ := eq83075 X0 X1
       grind)
    | (have i₁ := eq635 (M.op X1 X1)
       have i₂ := eq83075 X0 X1
       grind)
    | exact superpose eq83075 eq635
    | (have j1 := eq83075 X0 X1
       grind)
    | exact resolve eq635 eq83075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154337 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83075 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83075
  have eq154451 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154223 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq154223 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq154223
    | (have j0 := eq154223 X0 X1
       grind)
    | exact resolve eq154223 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154223
  have eq154454 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154220 X0 X1
       have i₂ := eq635 (M.op X0 X0)
       grind)
    | exact superpose eq635 eq154220
    | (have j0 := eq154220 X0 X1
       grind)
    | exact resolve eq154220 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154220
  have eq154742 : ∀ X0 X1 : G, (τ X1) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154451 X0 X1
       have i₂ := eq635 (M.op X0 X0)
       grind)
    | exact superpose eq635 eq154451
    | (have j0 := eq154451 X0 X1
       grind)
    | exact resolve eq154451 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154451
  have eq154745 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X1) (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154454 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq154454
    | (have j0 := eq154454 X0 X1
       grind)
    | exact resolve eq154454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154454
  have eq154813 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154742 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq154742 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq154742
    | (have j0 := eq154742 X0 X1
       grind)
    | exact resolve eq154742 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154742
  have eq154815 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154745 X0 X1
       have i₂ := eq609 (M.op X1 X1)
       grind)
    | exact superpose eq609 eq154745
    | (have j0 := eq154745 X0 X1
       grind)
    | exact resolve eq154745 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154745
  have eq154858 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154815 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq154815 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq154815
    | (have j0 := eq154815 X0 X1
       grind)
    | exact resolve eq154815 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154815
  have eq154892 : ∀ X0 X1 : G, X0 = X1 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154858 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq154858 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq154858
    | (have j0 := eq154858 X0 X1
       grind)
    | exact resolve eq154858 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154858
  have eq154920 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ X0 = X1 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154892 X0 X1
       have i₂ := eq635 (M.op X0 X0)
       grind)
    | exact superpose eq635 eq154892
    | (have j0 := eq154892 X0 X1
       grind)
    | exact resolve eq154892 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq154892
  have eq154939 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ X0 = X1 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq154920 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq154920 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq154920
    | (have j0 := eq154920 X0 X1
       grind)
    | exact resolve eq154920 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq154920
  have eq154946 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq154939 X0 X1
       have j1 := eq154337 X1 X0
       grind)
    | (have r₁ := eq154939 X1 X1
       have r₂ := eq154337 X0 X1
       grind)
    | (have r₁ := eq154939 (τ X1) (τ (M.op X1 X1))
       have r₂ := eq154337 X0 X1
       grind)
    | (have r₁ := eq154939 (τ (M.op X1 X1)) (τ X1)
       have r₂ := eq154337 X0 X1
       grind)
    | exact resolve eq154939 eq154337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154337 eq154939
  have eq154951 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (σ X0) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154946 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154946
    | (have j0 := eq154946 (τ (k (σ X0) X1)) (M.op X0 (τ X1))
       grind)
    | exact resolve eq154946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154946
  have eq155376 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (σ X0) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154951 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq154951
    | (have j0 := eq154951 X0 X1
       grind)
    | exact resolve eq154951 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154951
  have eq155901 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (σ X0) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq155376 X0 X1
       grind)
    | exact superpose eq155376 eq19
    | (have j1 := eq155376 X0 X1
       grind)
    | exact resolve eq19 eq155376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq155376
  have eq157857 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155901 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155901
    | (have j0 := eq155901 (M.op X1 X0) (k (σ X1) (σ X0))
       grind)
    | exact resolve eq155901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155901
  have eq158503 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157857 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq157857
    | (have j0 := eq157857 X0 X1
       grind)
    | exact resolve eq157857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157857
  have eq158617 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq158503 X0 X1
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq158503
    | (have j0 := eq158503 X0 X1
       grind)
    | exact resolve eq158503 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158503
  have eq158703 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq158617 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq158617
    | (have j0 := eq158617 X0 X1
       grind)
    | exact resolve eq158617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158617
  have eq158768 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq158703 X0 X1
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq158703
    | (have j0 := eq158703 X0 X1
       grind)
    | exact resolve eq158703 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158703
  have eq161693 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154813 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154813
    | exact resolve eq154813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154813
  have eq162125 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq161693 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq161693
    | (have j0 := eq161693 X0 X1
       grind)
    | exact resolve eq161693 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq161693
  have eq162580 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162125 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq162125
    | (have j0 := eq162125 X1 (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq162125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162125
  have eq162821 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162580 X0 X1
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq162580
    | (have j0 := eq162580 X0 X1
       grind)
    | exact resolve eq162580 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162580
  have eq162843 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162821 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq162821
    | (have j0 := eq162821 X0 X1
       grind)
    | exact resolve eq162821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162821
  have eq162862 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162843 X0 X1
       have i₂ := eq609 X0
       grind)
    | exact superpose eq609 eq162843
    | (have j0 := eq162843 X0 X1
       grind)
    | exact resolve eq162843 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162843
  have eq163191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq162862 (σ X1) (σ X0)
       grind)
    | exact superpose eq162862 eq15
    | (have j1 := eq162862 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq162862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162862
  have eq163348 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq163191 X0 X1
       have i₂ := eq566 X1
       grind)
    | exact superpose eq566 eq163191
    | (have j0 := eq163191 X0 X1
       grind)
    | exact resolve eq163191 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq163191
  have eq163463 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq163348 X0 X1
       have i₂ := eq609 X1
       grind)
    | exact superpose eq609 eq163348
    | (have j0 := eq163348 X0 X1
       grind)
    | exact resolve eq163348 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq163348
  have eq199029 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq163463 x y
       grind)
    | exact superpose eq163463 eq16
    | (have j1 := eq163463 x y
       grind)
    | exact resolve eq16 eq163463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163463
  have eq199776 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq199029
       have i₂ := eq158768 y x
       grind)
    | exact superpose eq158768 eq199029
    | (have j1 := eq158768 y x
       grind)
    | (have r₁ := eq199029
       have r₂ := eq158768 y x
       grind)
    | (have r₁ := eq199029
       have r₂ := eq158768 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq199029
       have r₂ := eq158768 (k x y) (M.op x y)
       grind)
    | exact resolve eq199029 eq158768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158768 eq199029
  have eq199779 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq199776
  have eq199780 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq199779
  have eq199787 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq199780
       grind)
    | exact superpose eq199780 eq10
    | exact resolve eq10 eq199780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199780
  have eq200124 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq199787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq199787
    | exact resolve eq199787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199787
  have eq200197 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200124
       grind)
    | exact superpose eq200124 eq16
    | exact resolve eq16 eq200124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200124
  have eq200198 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq200197
       have r₂ := eq795 x
       grind)
    | exact resolve eq200197 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq200197
  have eq203747 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq200198
       grind)
    | exact superpose eq200198 eq10
    | exact resolve eq10 eq200198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200198
  have eq204211 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq203747
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq203747
    | exact resolve eq203747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203747
  have eq204212 : x = (M.op y y) := by grind
  clear eq204211
  have eq204299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq835 y
       have i₂ := eq204212
       grind)
    | exact superpose eq204212 eq835
    | exact resolve eq835 eq204212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq204212
  have eq204654 : False := by grind
  exact eq204654

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq468 (σ X0)
       grind)
    | exact superpose eq468 eq15
    | (have j1 := eq468 (σ X0)
       grind)
    | exact resolve eq15 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq468 (τ X0)
       grind)
    | exact superpose eq468 eq18
    | (have j1 := eq468 (τ X0)
       grind)
    | exact resolve eq18 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq468
  have eq491 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq486 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq486
    | (have j0 := eq486 X0
       grind)
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq525 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq479
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
  have eq547 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
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
  have eq565 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
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
  have eq568 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq565 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq565
    | exact resolve eq565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq585 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq568 (τ X0)
       grind)
    | exact superpose eq568 eq32
    | exact resolve eq32 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq585 X0
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq585
    | exact resolve eq585 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq668 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq14 (τ X0) (τ X1)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq675 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 X1
       have i₂ := eq592 X1
       grind)
    | exact superpose eq592 eq668
    | (have j0 := eq668 X0 X1
       grind)
    | exact resolve eq668 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq699 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq592 X0
       grind)
    | exact superpose eq592 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq722 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq592 X1
       grind)
    | exact superpose eq592 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq808 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq547 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq547 X0 x
       grind)
    | exact superpose eq547 eq547
    | exact resolve eq547 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq834 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq808 X0
       have i₂ := eq568 (k X0 X0)
       grind)
    | exact superpose eq568 eq808
    | exact resolve eq808 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq844 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq834 X0
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq834
    | exact resolve eq834 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq850 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq844 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq844 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq844
    | exact resolve eq844 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq868 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq879 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq868 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq868
    | exact resolve eq868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq887 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq879
  have eq70333 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 (M.op X0 X0)
       have i₂ := eq722 X0 X1
       grind)
    | (have i₁ := eq491 (M.op X1 X1)
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq491
    | (have j0 := eq491 (M.op X0 X0)
       have j1 := eq722 X0 X1
       grind)
    | exact resolve eq491 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq70334 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (τ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq592 (M.op X0 X0)
       have i₂ := eq722 X0 X1
       grind)
    | (have i₁ := eq592 (M.op X1 X1)
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq592
    | (have j1 := eq722 X0 X1
       grind)
    | exact resolve eq592 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70399 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq70464 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70334 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq70334 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq70334
    | (have j0 := eq70334 X0 X1
       grind)
    | exact resolve eq70334 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70334
  have eq70465 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70333 X0 X1
       have i₂ := eq592 (M.op X0 X0)
       grind)
    | exact superpose eq592 eq70333
    | (have j0 := eq70333 X0 X1
       grind)
    | exact resolve eq70333 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70333
  have eq70664 : ∀ X0 X1 : G, (τ X1) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70464 X0 X1
       have i₂ := eq592 (M.op X0 X0)
       grind)
    | exact superpose eq592 eq70464
    | (have j0 := eq70464 X0 X1
       grind)
    | exact resolve eq70464 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70464
  have eq70665 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X1) (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70465 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq70465
    | (have j0 := eq70465 X0 X1
       grind)
    | exact resolve eq70465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70465
  have eq70693 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70664 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq70664 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq70664
    | (have j0 := eq70664 X0 X1
       grind)
    | exact resolve eq70664 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70664
  have eq70694 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70665 X0 X1
       have i₂ := eq568 (M.op X1 X1)
       grind)
    | exact superpose eq568 eq70665
    | (have j0 := eq70665 X0 X1
       grind)
    | exact resolve eq70665 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70665
  have eq70717 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70694 X0 X1
       have i₂ := eq62 X1 X1 X1
       grind)
    | (have i₁ := eq70694 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq62 eq70694
    | (have j0 := eq70694 X0 X1
       grind)
    | exact resolve eq70694 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70694
  have eq70733 : ∀ X0 X1 : G, X0 = X1 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70717 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq70717 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq70717
    | (have j0 := eq70717 X0 X1
       grind)
    | exact resolve eq70717 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70717
  have eq70745 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70733 X0 X1
       have i₂ := eq592 (M.op X0 X0)
       grind)
    | exact superpose eq592 eq70733
    | (have j0 := eq70733 X0 X1
       grind)
    | exact resolve eq70733 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq70733
  have eq70753 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70745 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq70745 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq70745
    | (have j0 := eq70745 X0 X1
       grind)
    | exact resolve eq70745 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq70745
  have eq70757 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70753 X0 X1
       have j1 := eq70399 X1 X0
       grind)
    | (have r₁ := eq70753 X1 X1
       have r₂ := eq70399 X0 X1
       grind)
    | (have r₁ := eq70753 (τ X1) (τ (M.op X1 X1))
       have r₂ := eq70399 X0 X1
       grind)
    | (have r₁ := eq70753 (τ (M.op X1 X1)) (τ X1)
       have r₂ := eq70399 X0 X1
       grind)
    | exact resolve eq70753 eq70399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70399 eq70753
  have eq70759 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70757 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70757
    | (have j0 := eq70757 (τ (k (σ X0) X1)) (M.op X0 (τ X1))
       grind)
    | exact resolve eq70757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70757
  have eq71083 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70759 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq70759
    | (have j0 := eq70759 X0 X1
       grind)
    | exact resolve eq70759 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70759
  have eq71491 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq71083 X0 X1
       grind)
    | exact superpose eq71083 eq19
    | (have j1 := eq71083 X0 X1
       grind)
    | exact resolve eq19 eq71083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq71083
  have eq73937 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71491 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71491
    | (have j0 := eq71491 X1 (σ X0)
       grind)
    | exact resolve eq71491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71491
  have eq74426 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73937 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq73937
    | (have j0 := eq73937 X0 X1
       grind)
    | exact resolve eq73937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73937
  have eq74519 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74426 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq74426
    | (have j0 := eq74426 X0 X1
       grind)
    | exact resolve eq74426 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74426
  have eq74586 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74519 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq74519
    | (have j0 := eq74519 X0 X1
       grind)
    | exact resolve eq74519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74519
  have eq74636 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74586 X0 X1
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq74586
    | (have j0 := eq74586 X0 X1
       grind)
    | exact resolve eq74586 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74586
  have eq78186 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70693 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70693
    | exact resolve eq70693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70693
  have eq78519 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78186 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq78186
    | (have j0 := eq78186 X0 X1
       grind)
    | exact resolve eq78186 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq78186
  have eq78874 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78519 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78519
    | (have j0 := eq78519 X1 (σ X0)
       grind)
    | exact resolve eq78519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78519
  have eq79059 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78874 X0 X1
       have i₂ := eq528 X0
       grind)
    | exact superpose eq528 eq78874
    | (have j0 := eq78874 X0 X1
       grind)
    | exact resolve eq78874 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78874
  have eq79076 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79059 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq79059
    | (have j0 := eq79059 X0 X1
       grind)
    | exact resolve eq79059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79059
  have eq79091 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79076 X0 X1
       have i₂ := eq568 X0
       grind)
    | exact superpose eq568 eq79076
    | (have j0 := eq79076 X0 X1
       grind)
    | exact resolve eq79076 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79076
  have eq79345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq79091 (σ X1) (σ X0)
       grind)
    | exact superpose eq79091 eq15
    | (have j1 := eq79091 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq79091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79091
  have eq79467 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79345 X0 X1
       have i₂ := eq528 X1
       grind)
    | exact superpose eq528 eq79345
    | (have j0 := eq79345 X0 X1
       grind)
    | exact resolve eq79345 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq79345
  have eq79567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79467 X0 X1
       have i₂ := eq568 X1
       grind)
    | exact superpose eq568 eq79467
    | (have j0 := eq79467 X0 X1
       grind)
    | exact resolve eq79467 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq79467
  have eq103904 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79567 x y
       grind)
    | exact superpose eq79567 eq16
    | (have j1 := eq79567 x y
       grind)
    | exact resolve eq16 eq79567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79567
  have eq104378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103904
       have i₂ := eq74636 y x
       grind)
    | exact superpose eq74636 eq103904
    | (have j1 := eq74636 y x
       grind)
    | (have r₁ := eq103904
       have r₂ := eq74636 y x
       grind)
    | (have r₁ := eq103904
       have r₂ := eq74636 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq103904
       have r₂ := eq74636 (k x y) (M.op x y)
       grind)
    | exact resolve eq103904 eq74636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74636 eq103904
  have eq104381 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq104378
  have eq104382 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq104381
  have eq104389 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq104382
       grind)
    | exact superpose eq104382 eq10
    | exact resolve eq10 eq104382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104382
  have eq104681 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104389
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq104389
    | exact resolve eq104389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104389
  have eq104740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104681
       grind)
    | exact superpose eq104681 eq16
    | exact resolve eq16 eq104681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104681
  have eq104741 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq104740
       have r₂ := eq850 x
       grind)
    | exact resolve eq104740 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq104740
  have eq104769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq887 y
       have i₂ := eq104741
       grind)
    | exact superpose eq104741 eq887
    | exact resolve eq887 eq104741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104741
  have eq104961 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq104769
       have r₂ := eq16
       grind)
    | exact resolve eq104769 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104769
  have eq105016 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq104961
       grind)
    | exact superpose eq104961 eq10
    | exact resolve eq10 eq104961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104961
  have eq105384 : x = (M.op y y) := by
    first
    | (have i₁ := eq105016
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq105016
    | exact resolve eq105016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105016
  have eq105565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq887 y
       have i₂ := eq105384
       grind)
    | exact superpose eq105384 eq887
    | exact resolve eq887 eq105384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq105384
  have eq105757 : False := by grind
  exact eq105757

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq25 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq24 X2 X0 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x x) X1
       have i₂ := eq24 x x x
       grind)
    | exact superpose eq24 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq24 (M.op X0 X0) (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq24 (M.op X1 X1) (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq122 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq48 (τ X0)
       grind)
    | exact superpose eq48 eq18
    | (have j1 := eq48 (τ X0)
       grind)
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq123 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq122
    | (have j0 := eq122 X0
       grind)
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq264 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 y x
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 y x
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X1) (σ X0) X2
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq24
    | (have j1 := eq61 X0 X1
       grind)
    | exact resolve eq24 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (σ X1) (σ X0) x
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq25
    | (have j1 := eq61 X0 X1
       grind)
    | exact resolve eq25 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq365 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq10
    | (have j1 := eq123 X0
       grind)
    | exact resolve eq10 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq475 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq88 (σ X0)
       grind)
    | exact superpose eq88 eq32
    | exact resolve eq32 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq564 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op (τ X0) X1) X2)) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (M.op (τ X0) X1) X2) (M.op (M.op (τ X0) X1) X2)) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op (M.op (τ X0) X1) X2)
       have i₂ := eq25 (τ X0) X1 X2
       grind)
    | exact superpose eq25 eq62
    | (have j0 := eq62 X0 (M.op (M.op (τ X0) X1) X2)
       grind)
    | exact resolve eq62 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq648 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq365
  have eq661 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq648 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq648
    | (have j0 := eq648 X0
       grind)
    | exact resolve eq648 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq648
  have eq662 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq668 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq662 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0) (τ X0)
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq24
    | exact resolve eq24 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq668 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq668
    | exact resolve eq668 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq702 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq700 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq700
    | exact resolve eq700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq703 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq264
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq264
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq264 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq704 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq703
  have eq713 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq702 (σ X0)
       grind)
    | exact superpose eq702 eq15
    | exact resolve eq15 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq713 X0
       have i₂ := eq702 X0
       grind)
    | exact superpose eq702 eq713
    | exact resolve eq713 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq826 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq702 X0
       grind)
    | exact superpose eq702 eq685
    | exact resolve eq685 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq838 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq826 (M.op X0 X0) (M.op x (τ X0))
       have i₂ := eq826 X0 x
       grind)
    | exact superpose eq826 eq826
    | exact resolve eq826 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq866 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq838 X0
       have i₂ := eq24 X0 X0 X0
       grind)
    | (have i₁ := eq838 X0
       have i₂ := eq24 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq24 eq838
    | exact resolve eq838 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq2395 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq268 X0 X1 X2
       have i₂ := eq727 X1
       grind)
    | exact superpose eq727 eq268
    | (have j0 := eq268 X0 X1 X2
       grind)
    | exact resolve eq268 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq2396 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2395 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq2395
    | (have j0 := eq2395 X0 X1 X2
       grind)
    | exact resolve eq2395 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2397 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2396 X0 X1 X2
       have i₂ := eq727 X1
       grind)
    | exact superpose eq727 eq2396
    | (have j0 := eq2396 X0 X1 X2
       grind)
    | exact resolve eq2396 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2561 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq269 X0 X1 X2
       have i₂ := eq727 X1
       grind)
    | exact superpose eq727 eq269
    | (have j0 := eq269 X0 X1 X2
       grind)
    | exact resolve eq269 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq2562 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2561 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq2561
    | (have j0 := eq2561 X0 X1 X2
       grind)
    | exact resolve eq2561 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2563 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2562 X0 X1 X2
       have i₂ := eq727 X1
       grind)
    | exact superpose eq727 eq2562
    | (have j0 := eq2562 X0 X1 X2
       grind)
    | exact resolve eq2562 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2595 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2563 X0 X1 (M.op (σ X0) x)
       have i₂ := eq2397 X0 X1 x
       grind)
    | exact superpose eq2397 eq2563
    | (have j0 := eq2563 X0 X1 x
       have j1 := eq2397 X0 X1 x
       grind)
    | exact resolve eq2563 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq2563
  have eq2615 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq3120 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (k X0 (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq475
    | exact resolve eq475 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq3121 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3120 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3120
    | exact resolve eq3120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3122 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3121 X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq3121
    | exact resolve eq3121 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq3121
  have eq3143 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (M.op X0 X0)) (σ X0))
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq11
    | exact resolve eq11 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq3218 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3143 (M.op x x)
       have i₂ := eq24 x x x
       grind)
    | exact superpose eq24 eq3143
    | exact resolve eq3143 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq3518 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 (M.op X0 X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ (M.op X0 X0)) x
       have i₂ := eq3218 X0
       grind)
    | exact superpose eq3218 eq25
    | exact resolve eq25 eq3218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5988 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2615 y x
       grind)
    | exact superpose eq2615 eq16
    | (have j1 := eq2615 x y
       grind)
    | exact resolve eq16 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq11473 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq704
       have i₂ := eq727 x
       grind)
    | exact superpose eq727 eq704
    | exact resolve eq704 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq11474 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11473
       have i₂ := eq727 y
       grind)
    | exact superpose eq727 eq11473
    | exact resolve eq11473 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11473
  have eq11475 : y = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11474
       have i₂ := eq727 x
       grind)
    | exact superpose eq727 eq11474
    | exact resolve eq11474 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11474
  have eq11478 : (M.op x y) = (k y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq11475
  have eq30908 : ∀ X0 X1 X2 : G, (τ (k X0 X0)) = (M.op (M.op (M.op (τ X0) X1) X2) (M.op (M.op (τ X0) X1) X2)) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op (τ X0) X1) X2)) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 X0 X1 X2
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq564
    | (have j0 := eq564 X0 X1 X2
       grind)
    | exact resolve eq564 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq30909 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (M.op (M.op (M.op (τ X0) X1) X2) (M.op (M.op (τ X0) X1) X2)) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op (τ X0) X1) X2)) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30908 X0 X1 X2
       have i₂ := eq702 X0
       grind)
    | exact superpose eq702 eq30908
    | (have j0 := eq30908 X0 X1 X2
       grind)
    | exact resolve eq30908 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30908
  have eq30910 : ∀ X0 X1 X2 : G, (τ (k X0 X0)) = (M.op (M.op (τ X0) X1) X2) ∨ (τ (M.op X0 X0)) = (M.op (M.op (M.op (τ X0) X1) X2) (M.op (M.op (τ X0) X1) X2)) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op (τ X0) X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30909 X0 X1 X2
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq30909
    | (have j0 := eq30909 X0 X1 X2
       grind)
    | exact resolve eq30909 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq30909
  have eq30911 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op (τ X0) X1) X2)) X0) ∨ (τ (M.op X0 X0)) = (M.op (M.op (M.op (τ X0) X1) X2) (M.op (M.op (τ X0) X1) X2)) ∨ (τ (M.op X0 X0)) = (M.op (M.op (τ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30910 X0 X1 X2
       have i₂ := eq702 X0
       grind)
    | exact superpose eq702 eq30910
    | (have j0 := eq30910 X0 X1 X2
       grind)
    | exact resolve eq30910 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30910
  have eq31029 : ∀ X0 X1 X2 : G, (k (τ (σ (M.op (M.op (τ (σ X0)) X1) X2))) X0) = (τ (σ (M.op (τ (σ X0)) X1))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op (τ (σ X0)) X1) X2) (M.op (M.op (τ (σ X0)) X1) X2)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ (M.op (M.op (τ (σ X0)) X1) X2)) X0
       have i₂ := eq30911 (σ X0) X1 X2
       grind)
    | exact superpose eq30911 eq23
    | (have j1 := eq30911 (σ X0) X1 X2
       grind)
    | exact resolve eq23 eq30911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30911
  have eq31096 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) X1) = (k (τ (σ (M.op (M.op (τ (σ X0)) X1) X2))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op (τ (σ X0)) X1) X2) (M.op (M.op (τ (σ X0)) X1) X2)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31029 X0 X1 X2
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq31029
    | (have j0 := eq31029 X0 X1 X2
       grind)
    | exact resolve eq31029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31029
  have eq31213 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) X1) = (k (M.op (M.op (τ (σ X0)) X1) X2) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op (τ (σ X0)) X1) X2) (M.op (M.op (τ (σ X0)) X1) X2)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31096 X0 X1 X2
       have i₂ := eq10 (M.op (M.op (τ (σ X0)) X1) X2)
       grind)
    | exact superpose eq10 eq31096
    | (have j0 := eq31096 X0 X1 X2
       grind)
    | exact resolve eq31096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31096
  have eq31294 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op (τ (σ X0)) X1) X2) (M.op (M.op (τ (σ X0)) X1) X2)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31213 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31213
    | (have j0 := eq31213 X0 X1 X2
       grind)
    | exact resolve eq31213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31213
  have eq31360 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31294 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31294
    | (have j0 := eq31294 X0 X1 X2
       grind)
    | exact resolve eq31294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31294
  have eq31401 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31360 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq31360
    | (have j0 := eq31360 X0 X1 X2
       grind)
    | exact resolve eq31360 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31360
  have eq31435 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31401 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31401
    | (have j0 := eq31401 X0 X1 X2
       grind)
    | exact resolve eq31401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31401
  have eq31458 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31435 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31435
    | (have j0 := eq31435 X0 X1 X2
       grind)
    | exact resolve eq31435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31435
  have eq31481 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31458 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq31458
    | (have j0 := eq31458 X0 X1 X2
       grind)
    | exact resolve eq31458 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31458
  have eq31499 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X0) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31481 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31481
    | (have j0 := eq31481 X0 X1 X2
       grind)
    | exact resolve eq31481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31481
  have eq178115 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5988
       have i₂ := eq11478
       grind)
    | exact superpose eq11478 eq5988
    | exact resolve eq5988 eq11478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988 eq11478
  have eq178149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq178115
  have eq178150 : (M.op x x) = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq178149
  have eq324124 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq31499 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq31499 eq24
    | (have j1 := eq31499 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq24 eq31499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31499
  have eq324364 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq324124 X0 X1
       have j1 := eq86 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq324124 X1 X1
       have r₂ := eq86 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq324124 X1 X1
       have r₂ := eq86 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq324124 X1 X1
       have r₂ := eq86 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq324124 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq324124
  have eq381458 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1 (M.op X0 X1)
       have i₂ := eq324364 X0 X1
       grind)
    | exact superpose eq324364 eq25
    | (have j1 := eq324364 X0 X1
       grind)
    | exact resolve eq25 eq324364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq381467 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1 (M.op X0 X1) X0
       have i₂ := eq324364 X0 X1
       grind)
    | exact superpose eq324364 eq82
    | (have j1 := eq324364 X0 X1
       grind)
    | exact resolve eq82 eq324364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq324364
  have eq387964 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = X0 ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq381458 (M.op X0 x) (M.op x x)
       have i₂ := eq24 X0 x x
       grind)
    | exact superpose eq24 eq381458
    | exact resolve eq381458 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381458
  have eq400058 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3518 (M.op X1 X0) X1
       have i₂ := eq387964 X0 X1
       grind)
    | exact superpose eq387964 eq3518
    | (have j1 := eq387964 X0 X1
       grind)
    | exact resolve eq3518 eq387964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq400123 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) = X0 ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq381467 (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq387964 X0 X1
       grind)
    | exact superpose eq387964 eq381467
    | (have j1 := eq387964 X0 X1
       grind)
    | exact resolve eq381467 eq387964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381467 eq387964
  have eq400126 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq400123 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400123
  have eq400128 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq400126 X0 X1
       have i₂ := eq9 (M.op X1 X0) X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq9 eq400126
    | (have j0 := eq400126 X0 X1
       grind)
    | exact resolve eq400126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400126
  have eq402656 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq400128 (M.op x x) (M.op X0 x)
       have i₂ := eq24 X0 x x
       grind)
    | exact superpose eq24 eq400128
    | exact resolve eq400128 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400128
  have eq488705 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op X1 (τ X0))) (M.op (σ (τ X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq400058 (τ X0) X1 X2
       have i₂ := eq866 X0
       grind)
    | exact superpose eq866 eq400058
    | (have j0 := eq400058 (τ X0) X1 X2
       grind)
    | exact resolve eq400058 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq400058
  have eq489253 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) ∨ (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq488705 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq488705
    | (have j0 := eq488705 X0 X1 X2
       grind)
    | exact resolve eq488705 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488705
  have eq641905 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (M.op X0 X0) (σ (M.op X1 (τ X0)))) ∨ (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X0 X0) (M.op X1 (τ X0))
       have i₂ := eq489253 X0 X1 X2
       grind)
    | exact superpose eq489253 eq18
    | (have j1 := eq489253 X0 X1 X2
       grind)
    | exact resolve eq18 eq489253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq489253
  have eq642173 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (σ (M.op X1 (τ X0)))) = X0 ∨ (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq641905 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq641905
    | (have j0 := eq641905 X0 X1 X2
       grind)
    | exact resolve eq641905 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641905
  have eq642833 : ∀ X0 X1 X2 : G, (σ X0) = (k (M.op (σ X0) (σ X0)) (σ (M.op X1 X0))) ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq642173 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq642173
    | exact resolve eq642173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642173
  have eq643314 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ (M.op X1 X0))) ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq642833 X0 X1 X2
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq642833
    | (have j0 := eq642833 X0 X1 X2
       grind)
    | exact resolve eq642833 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642833
  have eq643458 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (σ X0) = (σ (k (M.op X0 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq643314 X0 X1 X2
       have i₂ := eq15 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact superpose eq15 eq643314
    | (have j0 := eq643314 X0 X1 X2
       grind)
    | exact resolve eq643314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643314
  have eq1823228 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) (σ X0)) (σ (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k (M.op X0 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq402656 (σ (M.op X1 X0)) (M.op (σ X0) x)
       have i₂ := eq643458 X0 X1 x
       grind)
    | exact superpose eq643458 eq402656
    | (have j1 := eq643458 X0 X1 x
       grind)
    | exact resolve eq402656 eq643458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402656 eq643458
  have eq1823349 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k (M.op X0 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1823228 X0 X1
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq1823228
    | (have j0 := eq1823228 X0 X1
       grind)
    | exact resolve eq1823228 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823228
  have eq1823829 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X0) (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k (M.op X0 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1823349 X0 X1
       have i₂ := eq15 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact superpose eq15 eq1823349
    | (have j0 := eq1823349 X0 X1
       grind)
    | exact resolve eq1823349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823349
  have eq1823830 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X0) (M.op X1 X0))) ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1823829 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823829
  have eq1828075 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op X0 X0) (M.op X1 X0))
       have i₂ := eq1823830 X0 X1
       grind)
    | exact superpose eq1823830 eq10
    | (have j1 := eq1823830 X0 X1
       grind)
    | exact resolve eq10 eq1823830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823830
  have eq1828858 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1828075 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1828075
    | (have j0 := eq1828075 X0 X1
       grind)
    | exact resolve eq1828075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828075
  have eq1833219 : y = (k (M.op x x) (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1828858 y y
       have i₂ := eq178150
       grind)
    | exact superpose eq178150 eq1828858
    | exact resolve eq1828858 eq178150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178150 eq1828858
  have eq1833382 : y = (k (M.op x x) (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1833219
  have eq1833431 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1833382
       have i₂ := eq702 (M.op x x)
       grind)
    | exact superpose eq702 eq1833382
    | exact resolve eq1833382 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq1833382
  have eq1833666 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1833431
       have i₂ := eq24 x x x
       grind)
    | (have i₁ := eq1833431
       have i₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq24 eq1833431
    | exact resolve eq1833431 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833431
  have eq1840693 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1833666
       grind)
    | exact superpose eq1833666 eq16
    | exact resolve eq16 eq1833666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833666
  have eq1840694 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1840693
       have r₂ := eq727 x
       grind)
    | exact resolve eq1840693 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840693
  have eq1840843 : (M.op x x) = (τ (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1840694
       grind)
    | exact superpose eq1840694 eq10
    | exact resolve eq10 eq1840694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840694
  have eq1842006 : y = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1840843
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1840843
    | exact resolve eq1840843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840843
  have eq1845784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3218 x
       have i₂ := eq1842006
       grind)
    | exact superpose eq1842006 eq3218
    | exact resolve eq3218 eq1842006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218 eq1842006
  have eq1846466 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1845784
       have r₂ := eq16
       grind)
    | exact resolve eq1845784 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845784
  have eq1846644 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq727 (M.op y y)
       have i₂ := eq1846466
       grind)
    | exact superpose eq1846466 eq727
    | exact resolve eq727 eq1846466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846466
  have eq1847757 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq1846644
       have i₂ := eq24 y y y
       grind)
    | (have i₁ := eq1846644
       have i₂ := eq24 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq24 eq1846644
    | exact resolve eq1846644 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846644
  have eq1847975 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1847757
       have i₂ := eq727 (M.op x x)
       grind)
    | exact superpose eq727 eq1847757
    | exact resolve eq1847757 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847757
  have eq1848002 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1847975
       have i₂ := eq24 x x x
       grind)
    | (have i₁ := eq1847975
       have i₂ := eq24 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq24 eq1847975
    | exact resolve eq1847975 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1847975
  have eq1848024 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1848002
       grind)
    | exact superpose eq1848002 eq10
    | exact resolve eq10 eq1848002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848002
  have eq1849144 : x = y := by
    first
    | (have i₁ := eq1848024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1848024
    | exact resolve eq1848024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848024
  have eq1849352 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1849144
       grind)
    | exact superpose eq1849144 eq16
    | exact resolve eq16 eq1849144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849144
  have eq1849353 : False := by grind
  exact eq1849353

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  clear eq36
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq477 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq112
    | (have j0 := eq112 (σ X0)
       grind)
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq44
    | (have j1 := eq112 x
       grind)
    | exact resolve eq44 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq3402 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq17417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17417
    | exact resolve eq17417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17417
  have eq17429 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17418
       have r₂ := eq28
       grind)
    | exact resolve eq17418 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17418
  have eq17431 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17429
    | exact resolve eq17429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17429
  have eq17433 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17431 eq252
    | exact resolve eq252 eq17431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17434 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17431 eq262
    | exact resolve eq262 eq17431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17431
  have eq17527 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17434 eq17433
    | exact resolve eq17433 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17433 eq17434
  have eq17578 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq17527
  have eq17585 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq17578
  have eq17631 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17585
    | exact resolve eq17585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17585
  have eq17851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17631 eq91
    | exact resolve eq91 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq17631
  have eq17859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq17851
  have eq17861 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17859
       have r₂ := eq28
       grind)
    | exact resolve eq17859 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17859
  have eq17863 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq251 x
       have i₂ := eq17861
       grind)
    | exact superpose eq17861 eq251
    | exact resolve eq251 eq17861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq17864 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq261 y
       have i₂ := eq17861
       grind)
    | exact superpose eq17861 eq261
    | exact resolve eq261 eq17861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq17861
  have eq17963 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17864 eq17863
    | exact resolve eq17863 eq17864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17863 eq17864
  have eq18017 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17963
  have eq18025 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18017
  have eq18073 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18025
    | exact resolve eq18025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18025
  have eq18249 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq18073
       grind)
    | exact superpose eq18073 eq45
    | exact resolve eq45 eq18073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18073
  have eq18267 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18249
    | exact resolve eq18249 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18249
  have eq18344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18267 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq18267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18344
    | exact resolve eq18344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344
  have eq18358 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18347
       have r₂ := eq28
       grind)
    | exact resolve eq18347 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18347
  have eq18360 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18358
    | exact resolve eq18358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18358
  have eq33596 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18360 eq252
    | exact resolve eq252 eq18360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq33597 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18360 eq262
    | exact resolve eq262 eq18360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq18360
  have eq34387 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33597 eq33596
    | exact resolve eq33596 eq33597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33596 eq33597
  have eq34448 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34387
  have eq34728 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34448
  have eq34788 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq34728
    | exact resolve eq34728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34728
  have eq35142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34788 eq18267
    | exact resolve eq18267 eq34788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18267 eq34788
  have eq35160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq35142
  have eq35171 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq35160
       have r₂ := eq28
       grind)
    | exact resolve eq35160 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35160
  have eq35175 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq35171 eq30
    | exact resolve eq30 eq35171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35171
  have eq35303 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq35175
    | exact resolve eq35175 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35175
  have eq35304 : x = y := by grind
  clear eq35303
  have eq35305 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq35304
       grind)
    | exact superpose eq35304 eq19
    | exact resolve eq19 eq35304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq35306 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq35304
       grind)
    | exact superpose eq35304 eq25
    | exact resolve eq25 eq35304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq35304
  have eq35501 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq35306
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35306
    | exact resolve eq35306 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35306
  have eq35847 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35501 eq27
    | exact resolve eq27 eq35501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq35501
  have eq35989 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq481
       have i₂ := eq35305
       grind)
    | exact superpose eq35305 eq481
    | exact resolve eq481 eq35305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq35997 : (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  have eq36051 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq35989
    | exact resolve eq35989 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35989
  have eq36057 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq39628 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36051 eq112
    | (have j0 := eq112 (σ x)
       grind)
    | exact resolve eq112 eq36051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq39629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35847 eq39628
    | exact resolve eq39628 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39628
  have eq39641 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39629
       have r₂ := eq28
       grind)
    | exact resolve eq39629 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39629
  have eq39648 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35847 eq39641
    | exact resolve eq39641 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39641
  have eq39692 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39648 eq36057
    | exact resolve eq36057 eq39648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36057 eq39648
  have eq39693 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35847 eq39692
    | exact resolve eq39692 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39692
  have eq42483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39693 eq36051
    | exact resolve eq36051 eq39693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36051 eq39693
  have eq42487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42483
  have eq42489 : x = (M.op x y) := by
    first
    | (have r₁ := eq42487
       have r₂ := eq28
       grind)
    | exact resolve eq42487 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42487
  have eq42503 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq42489 eq21
    | exact resolve eq21 eq42489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq42653 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq42489 eq35997
    | exact resolve eq35997 eq42489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35997
  have eq42659 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq42653
       have i₂ := eq35305
       grind)
    | exact superpose eq35305 eq42653
    | exact resolve eq42653 eq35305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35305 eq42653
  have eq42758 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42503
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42503
    | exact resolve eq42503 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42503
  have eq42761 : x = (k x x) := by
    first
    | exact superpose eq42489 eq42659
    | exact resolve eq42659 eq42489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42489 eq42659
  have eq43173 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3402 x
       have i₂ := eq42761
       grind)
    | exact superpose eq42761 eq3402
    | (have j0 := eq3402 x
       grind)
    | exact resolve eq3402 eq42761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402 eq42761
  have eq43177 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq43173
  have eq43185 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43177
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43177
    | exact resolve eq43177 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43177
  have eq43197 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35847 eq43185
    | exact resolve eq43185 eq35847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35847 eq43185
  have eq43208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42758 eq43197
    | exact resolve eq43197 eq42758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42758 eq43197
  have eq43217 : False := by grind
  exact eq43217

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq229 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq85 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq85 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq256 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq258 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq256
    | (have j0 := eq256 X0 X1
       grind)
    | exact resolve eq256 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq261 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq258 X0 X1
       have j1 := eq252 X1 X0
       grind)
    | (have r₁ := eq258 X1 X0
       have r₂ := eq252 X0 X1
       grind)
    | (have r₁ := eq258 X1 (k X0 X1)
       have r₂ := eq252 X0 X1
       grind)
    | (have r₁ := eq258 X1 X1
       have r₂ := eq252 X1 X1
       grind)
    | exact resolve eq258 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq258
  have eq674 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261
    | exact resolve eq261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq261 y x
       grind)
    | exact superpose eq261 eq16
    | (have j1 := eq261 y x
       grind)
    | exact resolve eq16 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq707 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq674
    | (have j0 := eq674 X0 X1
       grind)
    | exact resolve eq674 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq674
  have eq709 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq707
    | exact resolve eq707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq770 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq709 (τ X0) X1
       grind)
    | exact superpose eq709 eq18
    | (have j1 := eq709 (τ X0) X1
       grind)
    | exact resolve eq18 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq709
  have eq1013 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq770 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq770
    | exact resolve eq770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1067 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1013 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1013
    | (have j0 := eq1013 X0 X1
       grind)
    | exact resolve eq1013 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1169 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq682
       have i₂ := eq1067 x y
       grind)
    | exact superpose eq1067 eq682
    | (have j1 := eq1067 (σ x) (σ y)
       grind)
    | (have r₁ := eq682
       have r₂ := eq1067 x y
       grind)
    | exact resolve eq682 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1169
  have eq1177 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1170
  have eq1242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq682
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq682
    | exact resolve eq682 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq1177
  have eq1243 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1242
  have eq1244 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1243
  have eq1313 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1244
  have eq1329 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1313
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1313
    | exact resolve eq1313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1620 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1329
       grind)
    | exact superpose eq1329 eq16
    | exact resolve eq16 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1641 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1620
       have i₂ := eq1067 x y
       grind)
    | exact superpose eq1067 eq1620
    | (have j1 := eq1067 x y
       grind)
    | (have r₁ := eq1620
       have r₂ := eq1067 x y
       grind)
    | exact resolve eq1620 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1642 : x = (M.op y y) := by grind
  clear eq1641
  have eq1683 : (M.op x y) = (k x y) := by grind
  clear eq1642
  have eq1777 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1620
       have i₂ := eq1683
       grind)
    | exact superpose eq1683 eq1620
    | exact resolve eq1620 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq1683
  have eq1780 : False := by grind
  exact eq1780

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq211 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X0 X2)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq346 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq372 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq618 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq618 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq634 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq632 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq632 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq632 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq671 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (k X0 (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq346 X0 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq346
    | exact resolve eq346 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq346 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq346
    | (have j0 := eq346 X0 y
       grind)
    | exact resolve eq346 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq720 : (k (k y y) y) = (τ (k (k (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq107 eq677
    | exact resolve eq677 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 : G, (k (k y y) (τ X0)) = (τ (k (k (σ y) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 (k y y) X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq372
    | exact resolve eq372 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq743 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq372
    | (have j0 := eq372 y X0
       grind)
    | exact resolve eq372 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq3390 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq10129 : ∀ X1 : G, y ≠ (M.op x y) ∨ (M.op y y) = (M.op X1 (M.op x y)) ∨ (M.op y y) = (k (M.op X1 (M.op x y)) y) := by
    intro X1
    first
    | exact superpose eq255 eq276
    | exact resolve eq276 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq11308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11308
    | exact resolve eq11308 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308
  have eq11327 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11316
       have r₂ := eq28
       grind)
    | exact resolve eq11316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11316
  have eq11329 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11327
    | exact resolve eq11327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327
  have eq11333 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq11329
  have eq11351 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11333
    | exact resolve eq11333 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11333
  have eq11380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11351 eq95
    | exact resolve eq95 eq11351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq11351
  have eq11395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11380
  have eq11397 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11395
       have r₂ := eq28
       grind)
    | exact resolve eq11395 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11395
  have eq11401 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11397
  have eq11419 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11401
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11401
    | exact resolve eq11401 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11401
  have eq11444 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11419
       grind)
    | exact superpose eq11419 eq45
    | exact resolve eq45 eq11419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq11419
  have eq11472 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11444
    | exact resolve eq11444 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11444
  have eq11777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11472 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11777
    | exact resolve eq11777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11777
  have eq11798 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11787
       have r₂ := eq28
       grind)
    | exact resolve eq11787 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11787
  have eq11800 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11798
    | exact resolve eq11798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11798
  have eq11801 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11800
  have eq12038 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11801
  have eq12056 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12038
    | exact resolve eq12038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12038
  have eq12172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12056 eq11472
    | exact resolve eq11472 eq12056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11472 eq12056
  have eq12181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12172
  have eq12185 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12181
       have r₂ := eq28
       grind)
    | exact resolve eq12181 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12189 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12185 eq116
    | (have r₁ := eq116
       have r₂ := eq12185
       grind)
    | exact resolve eq116 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq12198 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12185 eq256
    | exact resolve eq256 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq12206 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12189
  have eq13004 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12198 eq12198
    | exact resolve eq12198 eq12198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12198
  have eq13031 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13004
  have eq13072 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13031 eq281
    | exact resolve eq281 eq13031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13955 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13072 eq107
    | exact resolve eq107 eq13072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq14308 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13031 eq13955
    | exact resolve eq13955 eq13031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13955
  have eq14339 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq14308
  have eq14343 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq14339
    | exact resolve eq14339 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14339
  have eq14355 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq14343
       grind)
    | exact superpose eq14343 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq14343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14375 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq14355
  have eq14402 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq281 y
       have i₂ := eq14375
       grind)
    | exact superpose eq14375 eq281
    | exact resolve eq281 eq14375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14408 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 X0 y y
       have i₂ := eq14375
       grind)
    | exact superpose eq14375 eq53
    | exact resolve eq53 eq14375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq14375
  have eq16601 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (k (σ y) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq671 X0
       have i₂ := eq14343
       grind)
    | exact superpose eq14343 eq671
    | exact resolve eq671 eq14343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq16636 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (τ (k X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16601 X0
       have i₂ := eq677 X0
       grind)
    | exact superpose eq677 eq16601
    | exact resolve eq16601 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq16601
  have eq18137 : ∀ X0 : G, (k y (τ X0)) = (τ (k (k (σ y) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq737 X0
       have i₂ := eq14343
       grind)
    | exact superpose eq14343 eq737
    | exact resolve eq737 eq14343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq14343
  have eq18243 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (τ (k (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18137 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq18137
    | exact resolve eq18137 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq18137
  have eq19873 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = (σ (τ (k X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16636 eq15
    | exact resolve eq15 eq16636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16636
  have eq19960 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19873 X0
       have i₂ := eq15 (k X0 sF3)
       grind)
    | exact superpose eq15 eq19873
    | exact resolve eq19873 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19873
  have eq19976 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13072 eq19960
    | exact resolve eq19960 eq13072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19960
  have eq20012 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19976 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19976
  have eq20529 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20012 sF3
       have i₂ := eq281 sF3
       grind)
    | exact superpose eq281 eq20012
    | exact resolve eq20012 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23983 : ∀ X0 : G, (k (k (σ y) (σ y)) X0) = (σ (τ (k (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18243 eq15
    | exact resolve eq15 eq18243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18243
  have eq24078 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23983 X0
       have i₂ := eq15 (k sF3 X0)
       grind)
    | exact superpose eq15 eq23983
    | exact resolve eq23983 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23983
  have eq24106 : ∀ X0 : G, (k (σ y) X0) = (k (M.op (σ y) (σ y)) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13072 eq24078
    | exact resolve eq24078 eq13072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13072 eq24078
  have eq24174 : ∀ X0 : G, (k (σ y) X0) = (k (M.op (σ y) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24106
  have eq24429 : (k (σ y) (M.op (σ y) (σ y))) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24174 eq20012
    | exact resolve eq20012 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20012 eq24174
  have eq24460 : (k (σ y) (M.op (σ y) (σ y))) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24429
  have eq24490 : (k (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24460
  have eq24514 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24490
       have i₂ := eq281 sF3
       grind)
    | exact superpose eq281 eq24490
    | exact resolve eq24490 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24490
  have eq31020 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24514 eq14
    | exact resolve eq14 eq24514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24514
  have eq47262 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (k (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31020 eq281
    | exact resolve eq281 eq31020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq31020
  have eq47304 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47262
       have i₂ := eq267 sF3 sF3 sF3
       grind)
    | exact superpose eq267 eq47262
    | exact resolve eq47262 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq47262
  have eq69941 : (M.op (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20529 eq47304
    | exact resolve eq47304 eq20529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20529 eq47304
  have eq69956 : (M.op (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq69941
  have eq69980 : (τ (M.op (σ y) (σ y))) = (k (k y y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69956 eq720
    | exact resolve eq720 eq69956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq69956
  have eq70071 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69980
       have i₂ := eq14402
       grind)
    | exact superpose eq14402 eq69980
    | exact resolve eq69980 eq14402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14402 eq69980
  have eq70117 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ y = (M.op x y) := by grind
  clear eq70071
  have eq70128 : (τ (M.op (σ y) (σ y))) = (M.op (M.op y y) y) ∨ y = (M.op x y) := by grind
  clear eq70117
  have eq70941 : y = (M.op (τ (M.op (σ y) (σ y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14408 (M.op y y)
       have i₂ := eq70128
       grind)
    | exact superpose eq70128 eq14408
    | exact resolve eq14408 eq70128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70128
  have eq70959 : y = (M.op (τ (M.op (σ y) (σ y))) y) ∨ y = (M.op x y) := by grind
  clear eq70941
  have eq91560 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12206 eq61
    | exact resolve eq61 eq12206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq12206
  have eq157688 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13031 eq91560
    | exact resolve eq91560 eq13031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13031 eq91560
  have eq157982 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq157688
  have eq157990 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq157982
    | exact resolve eq157982 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq157982
  have eq158009 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq157990
       grind)
    | exact superpose eq157990 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq157990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157990
  have eq158021 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq158009
  have eq158034 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq158021
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq158021
    | exact resolve eq158021 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158021
  have eq158035 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq158034
  have eq158194 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14408 y
       have i₂ := eq158035
       grind)
    | exact superpose eq158035 eq14408
    | exact resolve eq14408 eq158035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14408 eq158035
  have eq158215 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq158194
  have eq158337 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq158215
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq158215
    | exact resolve eq158215 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158215
  have eq158338 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq158337
  have eq158423 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq158338 eq27
    | exact resolve eq27 eq158338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158338
  have eq159871 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq158423 eq266
    | exact resolve eq266 eq158423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq158423
  have eq160128 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12185 eq159871
    | exact resolve eq159871 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12185 eq159871
  have eq160156 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq160128
  have eq160621 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq160156 eq70959
    | exact resolve eq70959 eq160156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70959 eq160156
  have eq160731 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) := by grind
  clear eq160621
  have eq160848 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq160731
    | exact resolve eq160731 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq160731
  have eq160899 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq160848
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq160848
    | exact resolve eq160848 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq160848
  have eq160900 : y = (M.op x y) := by grind
  clear eq160899
  have eq160902 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq160900 eq21
    | exact resolve eq21 eq160900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq160953 : x = (M.op (M.op y x) y) := by
    first
    | exact superpose eq160900 eq211
    | exact resolve eq211 eq160900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq160963 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq160900 eq255
    | exact resolve eq255 eq160900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq161198 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq160902
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq160902
    | exact resolve eq160902 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160902
  have eq161202 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq161198 eq27
    | exact resolve eq27 eq161198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq161801 : y = (M.op y y) := by
    first
    | (have i₁ := eq160963 (M.op y x)
       have i₂ := eq160963 x
       grind)
    | exact superpose eq160963 eq160963
    | exact resolve eq160963 eq160963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160963
  have eq161992 : (k y y) = (M.op y y) := by grind
  have eq162019 : y = (k y y) := by
    first
    | (have i₁ := eq161992
       have i₂ := eq161801
       grind)
    | exact superpose eq161801 eq161992
    | exact resolve eq161992 eq161801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161992
  have eq162124 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq638 y y
       have i₂ := eq162019
       grind)
    | exact superpose eq162019 eq638
    | (have j0 := eq638 y y
       grind)
    | exact resolve eq638 eq162019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq162019
  have eq162130 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq162124
  have eq162131 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq162130
  have eq162145 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq162131
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq162131
    | exact resolve eq162131 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162131
  have eq162169 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq161198 eq162145
    | exact resolve eq162145 eq161198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162145
  have eq163141 : ∀ X1 : G, (M.op y y) = (M.op X1 (M.op x y)) ∨ (M.op y y) = (k (M.op X1 (M.op x y)) y) := by
    intro X1
    first
    | (have j0 := eq10129 X1
       grind)
    | (have r₁ := eq10129 X1
       have r₂ := eq160900
       grind)
    | exact resolve eq10129 eq160900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10129
  have eq163142 : ∀ X1 : G, (M.op y y) = (M.op X1 y) ∨ (M.op y y) = (k (M.op X1 (M.op x y)) y) := by
    intro X1
    first
    | exact superpose eq160900 eq163141
    | (have j0 := eq163141 X1
       grind)
    | exact resolve eq163141 eq160900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163141
  have eq163143 : ∀ X1 : G, y = (M.op X1 y) ∨ (M.op y y) = (k (M.op X1 (M.op x y)) y) := by
    intro X1
    first
    | (have i₁ := eq163142 X1
       have i₂ := eq161801
       grind)
    | exact superpose eq161801 eq163142
    | (have j0 := eq163142 X1
       grind)
    | exact resolve eq163142 eq161801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163142
  have eq163144 : ∀ X1 : G, (M.op y y) = (k (M.op X1 y) y) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | exact superpose eq160900 eq163143
    | (have j0 := eq163143 X1
       grind)
    | exact resolve eq163143 eq160900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160900 eq163143
  have eq163145 : ∀ X1 : G, y = (k (M.op X1 y) y) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq163144 X1
       have i₂ := eq161801
       grind)
    | exact superpose eq161801 eq163144
    | (have j0 := eq163144 X1
       grind)
    | exact resolve eq163144 eq161801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161801 eq163144
  have eq163199 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq163145 (M.op y x)
       have i₂ := eq160953
       grind)
    | exact superpose eq160953 eq163145
    | exact resolve eq163145 eq160953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160953 eq163145
  have eq163320 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3390 x
       have i₂ := eq163199
       grind)
    | exact superpose eq163199 eq3390
    | (have j0 := eq3390 x
       grind)
    | exact resolve eq3390 eq163199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390 eq163199
  have eq163349 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq163320
       have r₂ := eq25
       grind)
    | exact resolve eq163320 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163320
  have eq163374 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq161198 eq163349
    | exact resolve eq163349 eq161198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163349
  have eq163396 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq163374
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq163374
    | exact resolve eq163374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163374
  have eq163416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq161202 eq163396
    | exact resolve eq163396 eq161202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163396
  have eq163425 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq163416
       have r₂ := eq28
       grind)
    | exact resolve eq163416 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163416
  have eq163432 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq161198 eq163425
    | exact resolve eq163425 eq161198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163425
  have eq163439 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq162169 eq163432
    | exact resolve eq163432 eq162169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163432
  have eq163446 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq163439
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq163439
    | exact resolve eq163439 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163439
  have eq163620 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq163446 eq161202
    | exact resolve eq161202 eq163446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163446
  have eq163630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq162169 eq163620
    | exact resolve eq163620 eq162169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163620
  have eq163709 : x = y := by
    first
    | (have r₁ := eq163630
       have r₂ := eq28
       grind)
    | exact resolve eq163630 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163630
  have eq163882 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq163709
       grind)
    | exact superpose eq163709 eq25
    | exact resolve eq25 eq163709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq163709
  have eq164634 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq161198 eq163882
    | exact resolve eq163882 eq161198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161198 eq163882
  have eq164909 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq164634
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164634
    | exact resolve eq164634 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq164634
  have eq165329 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq164909 eq161202
    | exact resolve eq161202 eq164909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161202 eq164909
  have eq165338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq162169 eq165329
    | exact resolve eq165329 eq162169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162169 eq165329
  have eq165416 : False := by grind
  exact eq165416
