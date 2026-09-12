import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_x_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq40 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45 (M.op X0 X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq45
    | exact resolve eq45 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq28
    | exact resolve eq28 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq81 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq85 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ X0)
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq85 (σ X0)
       grind)
    | exact superpose eq85 eq28
    | (have j1 := eq85 (σ X0)
       grind)
    | exact resolve eq28 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq85 (τ X0)
       grind)
    | exact superpose eq85 eq17
    | (have j1 := eq85 (τ X0)
       grind)
    | exact resolve eq17 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq139 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq138
    | (have j0 := eq138 X0
       grind)
    | exact resolve eq138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq140 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq136 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | (have j0 := eq136 X0
       grind)
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq147 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq161 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 (M.op X0 X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq54
    | exact resolve eq54 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 X2 (M.op X0 X1) X1
       have i₂ := eq43 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq39 X1 X1 X0 X2
       grind)
    | exact superpose eq39 eq54
    | exact resolve eq54 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq591 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq561 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq561
    | exact resolve eq561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq624 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq591
    | exact resolve eq591 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) ≠ (M.op X2 X2) ∨ (M.op X2 (σ X1)) = X2 ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq147 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) X1
       have i₂ := eq147 X0 X1
       grind)
    | exact superpose eq147 eq13
    | (have j0 := eq13 (σ X0) X2
       have j1 := eq147 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq147 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq147 X0 X1
       grind)
    | exact resolve eq13 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X1)
       have i₂ := eq147 X1 X0
       grind)
    | (have i₁ := eq40 (σ X1)
       have i₂ := eq147 X0 X1
       grind)
    | exact superpose eq147 eq40
    | (have j1 := eq147 X1 X0
       grind)
    | exact resolve eq40 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq814 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X1 X0)
       have i₂ := eq624 X0 X1
       grind)
    | exact superpose eq624 eq40
    | exact resolve eq40 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 X1 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq814 X0 X1
       grind)
    | exact superpose eq814 eq39
    | exact resolve eq39 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq874 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq854 X0 X1 X2
       have i₂ := eq624 X1 X0
       grind)
    | exact superpose eq624 eq854
    | exact resolve eq854 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq963 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq591 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq874 X0 X1 X2
       grind)
    | exact superpose eq874 eq591
    | exact resolve eq591 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq969 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq963 X0 X1 X2
       have i₂ := eq624 X1 X2
       grind)
    | exact superpose eq624 eq963
    | exact resolve eq963 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1451 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq81
    | (have j1 := eq131 X0
       grind)
    | exact resolve eq81 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 (σ X0) (σ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq43
    | (have j1 := eq131 X0
       grind)
    | exact resolve eq43 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1477 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 (σ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq40
    | (have j1 := eq131 X0
       grind)
    | exact resolve eq40 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1486 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1499 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1451 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1451
    | (have j0 := eq1451 X0
       grind)
    | exact resolve eq1451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1510 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq560 X0 X1 X2
       have i₂ := eq969 X0 X1 X0
       grind)
    | exact superpose eq969 eq560
    | exact resolve eq560 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq969
  have eq1520 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op X0 X0) X3)) = (M.op X0 (M.op (M.op X0 X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1510 (M.op X0 X0) X3 (M.op x (M.op X0 x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1510
    | exact resolve eq1510 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2100 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq139 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139
    | exact resolve eq139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq2126 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2100 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2100
    | (have j0 := eq2100 X0
       grind)
    | exact resolve eq2100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2147 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (k X0 X0) X1
       have i₂ := eq2126 X0
       grind)
    | exact superpose eq2126 eq28
    | (have j1 := eq2126 X0
       grind)
    | exact resolve eq28 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2162 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2147 X0 X1
       have i₂ := eq28 (M.op X0 X0) X1
       grind)
    | exact superpose eq28 eq2147
    | (have j0 := eq2147 X0 X1
       grind)
    | exact resolve eq2147 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2147
  have eq2203 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1520 X0 (M.op X0 X1)
       have i₂ := eq1510 X0 X1 X0
       grind)
    | (have i₁ := eq1520 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq1510 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq1510 eq1520
    | exact resolve eq1520 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq2309 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2203 X0 X1
       have i₂ := eq814 X0 X1
       grind)
    | exact superpose eq814 eq2203
    | exact resolve eq2203 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq2348 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2309 X2 X1
       have i₂ := eq1510 X1 X2 X0
       grind)
    | (have i₁ := eq2309 (M.op X2 X0) X0
       have i₂ := eq1510 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1510 eq2309
    | exact resolve eq2309 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq2623 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 (M.op X0 X1)
       have i₂ := eq2348 X2 X0 X1
       grind)
    | exact superpose eq2348 eq9
    | exact resolve eq9 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2678 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2623 X0 X1 X2
       have i₂ := eq624 X0 X2
       grind)
    | exact superpose eq624 eq2623
    | exact resolve eq2623 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq2623
  have eq2767 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2678 X2 X3 X1
       have i₂ := eq1510 X1 X2 X0
       grind)
    | (have i₁ := eq2678 (M.op X2 X0) X1 X0
       have i₂ := eq1510 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1510 eq2678
    | exact resolve eq2678 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510 eq2678
  have eq3813 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq1499 X0
       grind)
    | exact superpose eq1499 eq81
    | (have j1 := eq1499 X0
       grind)
    | exact resolve eq81 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1499
  have eq3895 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3813 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3813
    | (have j0 := eq3813 X0
       grind)
    | exact resolve eq3813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813
  have eq8092 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op (σ X1) (σ X1)) (σ X0)
       have i₂ := eq727 X1 X0
       grind)
    | exact superpose eq727 eq43
    | (have j1 := eq727 X1 X0
       grind)
    | exact resolve eq43 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq8161 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8092 X0 X1
       have i₂ := eq43 (σ X1) (σ X1)
       grind)
    | exact superpose eq43 eq8092
    | (have j0 := eq8092 X0 X1
       grind)
    | exact resolve eq8092 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8092
  have eq11857 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq725 X0 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq11858 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11857
  have eq11859 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11858 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq11858
    | (have j0 := eq11858 X0 X1
       grind)
    | exact resolve eq11858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11858
  have eq33811 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1477 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1477
    | (have j0 := eq1477 (τ X0)
       grind)
    | exact resolve eq1477 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq33956 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33811 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33811
    | (have j0 := eq33811 X0
       grind)
    | exact resolve eq33811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33811
  have eq33971 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33956 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33956
    | (have j0 := eq33956 X0
       grind)
    | exact resolve eq33956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33956
  have eq34025 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op (M.op X2 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2767 X0 X0 (k X0 X0) x
       have i₂ := eq33971 X0
       grind)
    | exact superpose eq33971 eq2767
    | (have j1 := eq33971 X0
       grind)
    | exact resolve eq2767 eq33971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767 eq33971
  have eq34117 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34025 X0 X1 x
       have i₂ := eq161 X0 x
       grind)
    | exact superpose eq161 eq34025
    | (have j0 := eq34025 X0 X1 x
       grind)
    | exact resolve eq34025 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34025
  have eq52454 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1458 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1458
    | (have j0 := eq1458 (τ X0)
       grind)
    | exact resolve eq1458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52473 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq140 (k X0 X0)
       have i₂ := eq1458 X0
       grind)
    | exact superpose eq1458 eq140
    | (have j0 := eq140 X0
       have j1 := eq1458 X0
       grind)
    | exact resolve eq140 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1458
  have eq52717 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq52473 X0
       have j1 := eq1486 X0
       grind)
    | (have r₁ := eq52473 X0
       have r₂ := eq1486 X0
       grind)
    | exact resolve eq52473 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52473
  have eq52726 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq52454 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52454
    | (have j0 := eq52454 X0
       grind)
    | exact resolve eq52454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52454
  have eq52734 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq52717 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52717
    | (have j0 := eq52717 X0
       grind)
    | exact resolve eq52717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52717
  have eq52739 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52726 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52726
    | (have j0 := eq52726 X0
       grind)
    | exact resolve eq52726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52726
  have eq52754 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (k X0 X0) X1
       have i₂ := eq52739 X0
       grind)
    | exact superpose eq52739 eq43
    | (have j1 := eq52739 X0
       grind)
    | exact resolve eq43 eq52739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52739
  have eq54189 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34117 X0 (k (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq52754 (M.op X0 X0) (k X0 X0)
       grind)
    | exact superpose eq52754 eq34117
    | (have j0 := eq34117 X0 x
       have j1 := eq52754 X0 x
       grind)
    | exact resolve eq34117 eq52754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34117 eq52754
  have eq54586 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54189 X0
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq54189
    | (have j0 := eq54189 X0
       grind)
    | exact resolve eq54189 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54189
  have eq54587 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq54586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54586
  have eq57227 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (τ X0) X0 (k (τ X0) (τ X0))
       have i₂ := eq52734 (τ X0)
       grind)
    | exact superpose eq52734 eq27
    | (have j1 := eq52734 (τ X0)
       grind)
    | exact resolve eq27 eq52734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52734
  have eq57294 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57227 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq57227
    | (have j0 := eq57227 X0
       grind)
    | exact resolve eq57227 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57227
  have eq57304 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57294 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57294
    | (have j0 := eq57294 X0
       grind)
    | exact resolve eq57294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57294
  have eq57311 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57304 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57304
    | (have j0 := eq57304 X0
       grind)
    | exact resolve eq57304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57304
  have eq57321 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq27 (τ X0) X0 (k (τ X0) (τ X0))
       have i₂ := eq57311 (τ X0)
       grind)
    | exact superpose eq57311 eq27
    | (have j1 := eq57311 (τ X0)
       grind)
    | exact resolve eq27 eq57311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq57341 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3895 (k X0 X0)
       have i₂ := eq57311 X0
       grind)
    | exact superpose eq57311 eq3895
    | (have j0 := eq3895 X0
       have j1 := eq57311 X0
       grind)
    | exact resolve eq3895 eq57311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq57387 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq57341 X0
       have j1 := eq12 (k X0 X0) X0
       grind)
    | (have r₁ := eq57341 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq57341 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57341
  have eq57394 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57321 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq57321
    | (have j0 := eq57321 X0
       grind)
    | exact resolve eq57321 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57321
  have eq57404 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57394 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57394
    | (have j0 := eq57394 X0
       grind)
    | exact resolve eq57394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57394
  have eq62642 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ (k X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57404 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq57404
    | (have j0 := eq57404 (σ X0)
       grind)
    | exact resolve eq57404 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57404
  have eq62726 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) (k X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq62642 X0
       have i₂ := eq15 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq15 eq62642
    | (have j0 := eq62642 X0
       grind)
    | exact resolve eq62642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62642
  have eq62735 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62726 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62726
    | (have j0 := eq62726 X0
       grind)
    | exact resolve eq62726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62726
  have eq77869 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (k (k X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2162 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2162
    | (have j0 := eq2162 X1 X1
       grind)
    | exact resolve eq2162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77907 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57387 (τ X0)
       have i₂ := eq2162 (τ X0) X0
       grind)
    | exact superpose eq2162 eq57387
    | (have j0 := eq57387 (τ X0)
       have j1 := eq2162 (τ X0) x
       grind)
    | exact resolve eq57387 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq77937 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq77907 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq77907 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq77907 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77907
  have eq77957 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77937 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq77937
    | (have j0 := eq77937 X0
       grind)
    | exact resolve eq77937 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77937
  have eq77973 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77957 X0
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq77957
    | (have j0 := eq77957 X0
       grind)
    | exact resolve eq77957 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77957
  have eq77979 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77973 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq77973
    | (have j0 := eq77973 X0
       grind)
    | exact resolve eq77973 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq77973
  have eq78026 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57387 X0
       have i₂ := eq77869 X0 X0
       grind)
    | exact superpose eq77869 eq57387
    | (have j0 := eq57387 X0
       have j1 := eq77869 X0 X0
       grind)
    | exact resolve eq57387 eq77869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57387
  have eq78037 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62735 X0
       have i₂ := eq77869 (k X0 X0) X0
       grind)
    | exact superpose eq77869 eq62735
    | (have j0 := eq62735 X0
       have j1 := eq77869 X0 X0
       grind)
    | exact resolve eq62735 eq77869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62735 eq77869
  have eq78155 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78037
  have eq78185 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78026 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq78026 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq78026 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78026
  have eq78200 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78185 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq78185
    | (have j0 := eq78185 X0
       grind)
    | exact resolve eq78185 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78185
  have eq78205 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78200 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq78200
    | exact resolve eq78200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78208 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78200 (k X0 X0)
       have i₂ := eq57311 X0
       grind)
    | exact superpose eq57311 eq78200
    | (have j0 := eq78200 X0
       have j1 := eq57311 X0
       grind)
    | exact resolve eq78200 eq57311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57311 eq78200
  have eq78373 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78208 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq78208 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq78208 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78208
  have eq78839 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 (k X0 X0)
       have i₂ := eq78373 X0
       grind)
    | exact superpose eq78373 eq40
    | (have j1 := eq78373 X0
       grind)
    | exact resolve eq40 eq78373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78898 : ∀ X0 : G, (M.op X0 (M.op (k X0 X0) X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq814 (k X0 X0) (k X0 X0)
       have i₂ := eq78373 X0
       grind)
    | exact superpose eq78373 eq814
    | (have j1 := eq78373 X0
       grind)
    | exact resolve eq814 eq78373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq78373
  have eq95039 : ∀ X0 : G, (σ (τ X0)) = (σ (k (τ (k X0 X0)) (k (τ X0) (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78155 (τ X0)
       have i₂ := eq77979 X0
       grind)
    | exact superpose eq77979 eq78155
    | (have j1 := eq77979 X0
       grind)
    | exact resolve eq78155 eq77979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77979 eq78155
  have eq95214 : ∀ X0 : G, (σ (τ X0)) = (σ (k (τ (k X0 X0)) (k (τ X0) (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq95039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95039
  have eq95267 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 X0) (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95214 X0
       have i₂ := eq17 (k X0 X0) (k (τ X0) (τ X0))
       grind)
    | exact superpose eq17 eq95214
    | (have j0 := eq95214 X0
       grind)
    | exact resolve eq95214 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95214
  have eq95301 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 X0) (k X0 (σ (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95267 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq95267
    | (have j0 := eq95267 X0
       grind)
    | exact resolve eq95267 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq95267
  have eq95325 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95301 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95301
    | (have j0 := eq95301 X0
       grind)
    | exact resolve eq95301 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95301
  have eq95357 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (σ X0) (k (σ X0) (σ X0))
       have i₂ := eq95325 (σ X0)
       grind)
    | exact superpose eq95325 eq71
    | (have j1 := eq95325 (σ X0)
       grind)
    | exact resolve eq71 eq95325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95325
  have eq95462 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq95357 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq95357
    | (have j0 := eq95357 X0
       grind)
    | exact resolve eq95357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95357
  have eq95472 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq95462 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95462
    | (have j0 := eq95462 X0
       grind)
    | exact resolve eq95462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95462
  have eq95481 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq95472 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq95472
    | (have j0 := eq95472 X0
       grind)
    | exact resolve eq95472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95472
  have eq95490 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95481 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95481
    | (have j0 := eq95481 X0
       grind)
    | exact resolve eq95481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95481
  have eq95511 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (σ X0) (k (σ X0) (σ X0))
       have i₂ := eq95490 (σ X0)
       grind)
    | exact superpose eq95490 eq71
    | (have j1 := eq95490 (σ X0)
       grind)
    | exact resolve eq71 eq95490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq95490
  have eq95651 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95511 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq95511
    | (have j0 := eq95511 X0
       grind)
    | exact resolve eq95511 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95511
  have eq95662 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95651 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95651
    | (have j0 := eq95651 X0
       grind)
    | exact resolve eq95651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95651
  have eq95670 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95662 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq95662
    | (have j0 := eq95662 X0
       grind)
    | exact resolve eq95662 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95662
  have eq97114 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 (σ X0)
       have i₂ := eq78205 X0
       grind)
    | exact superpose eq78205 eq40
    | (have j1 := eq78205 X0
       grind)
    | exact resolve eq40 eq78205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78205
  have eq105698 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq8161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8161
  have eq105707 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105698 X0 X1
       have j1 := eq11859 X1 X0
       grind)
    | (have r₁ := eq105698 X1 X1
       have r₂ := eq11859 X1 X1
       grind)
    | (have r₁ := eq105698 X1 X0
       have r₂ := eq11859 X0 X1
       grind)
    | exact resolve eq105698 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11859 eq105698
  have eq107293 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq105707 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq105707
    | exact resolve eq105707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107384 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105707 x y
       grind)
    | exact superpose eq105707 eq16
    | (have j1 := eq105707 x y
       grind)
    | exact resolve eq16 eq105707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105707
  have eq107710 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107293 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq107293
    | (have j0 := eq107293 X0 X1
       grind)
    | exact resolve eq107293 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq107293
  have eq107796 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107710 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107710
    | exact resolve eq107710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107710
  have eq109583 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq107384
       have i₂ := eq107796 x y
       grind)
    | exact superpose eq107796 eq107384
    | (have j1 := eq107796 (σ x) (σ y)
       grind)
    | exact resolve eq107384 eq107796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107384
  have eq109592 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq109583
  have eq109616 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq109592
       grind)
    | exact superpose eq109592 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq109592
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq109592
       grind)
    | exact resolve eq12 eq109592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109592
  have eq109773 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq109616
  have eq109820 : (σ x) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq109773
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq109773
    | exact resolve eq109773 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109773
  have eq109844 : (k x y) = (τ (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq109820
       grind)
    | exact superpose eq109820 eq10
    | exact resolve eq10 eq109820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109820
  have eq110001 : x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq109844
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq109844
    | exact resolve eq109844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109844
  have eq110002 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq110001
       have r₂ := eq12 x y
       grind)
    | exact resolve eq110001 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110001
  have eq110003 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110002
       have i₂ := eq107796 x y
       grind)
    | exact superpose eq107796 eq110002
    | (have j1 := eq107796 x y
       grind)
    | exact resolve eq110002 eq107796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107796 eq110002
  have eq110027 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq161 x y
       have i₂ := eq110003
       grind)
    | exact superpose eq110003 eq161
    | exact resolve eq161 eq110003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110745 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110003
       have i₂ := eq110027
       grind)
    | exact superpose eq110027 eq110003
    | exact resolve eq110003 eq110027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110003 eq110027
  have eq110907 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq110745
  have eq110935 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq110907
       grind)
    | exact superpose eq110907 eq40
    | exact resolve eq40 eq110907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq110907
  have eq111163 : x = (M.op x y) := by grind
  clear eq110935
  have eq111211 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq161 y x
       have i₂ := eq111163
       grind)
    | exact superpose eq111163 eq161
    | exact resolve eq161 eq111163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq111220 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq874 X0 y x
       have i₂ := eq111163
       grind)
    | exact superpose eq111163 eq874
    | exact resolve eq874 eq111163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq111396 : x = (M.op y y) := by
    first
    | (have i₁ := eq111211
       have i₂ := eq111163
       grind)
    | exact superpose eq111163 eq111211
    | exact resolve eq111211 eq111163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111211
  have eq111493 : y = (M.op x x) := by
    first
    | (have i₁ := eq43 y y
       have i₂ := eq111396
       grind)
    | exact superpose eq111396 eq43
    | exact resolve eq43 eq111396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq111396
  have eq111978 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq54587 x
       have i₂ := eq111493
       grind)
    | exact superpose eq111493 eq54587
    | exact resolve eq54587 eq111493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54587 eq111493
  have eq127237 : (M.op x y) = (M.op (k y y) y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq111220 (k y y)
       have i₂ := eq78898 y
       grind)
    | exact superpose eq78898 eq111220
    | (have j1 := eq78898 y
       grind)
    | exact resolve eq111220 eq78898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78898 eq111220
  have eq127623 : x = (M.op (k y y) y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq127237
       have i₂ := eq111163
       grind)
    | exact superpose eq111163 eq127237
    | exact resolve eq127237 eq111163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127237
  have eq151924 : x = (k y y) ∨ y = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq78839 y
       have i₂ := eq127623
       grind)
    | exact superpose eq127623 eq78839
    | (have j0 := eq78839 y
       grind)
    | exact resolve eq78839 eq127623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78839 eq127623
  have eq152124 : y = (k y y) ∨ x = (k y y) := by grind
  clear eq151924
  have eq152344 : x ≠ y ∨ x = (k y y) := by grind
  clear eq152124
  have eq152359 : x = (k y y) := by
    first
    | (have r₁ := eq152344
       have r₂ := eq111978
       grind)
    | exact resolve eq152344 eq111978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111978 eq152344
  have eq152460 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1486 y
       have i₂ := eq152359
       grind)
    | exact superpose eq152359 eq1486
    | (have j0 := eq1486 y
       grind)
    | exact resolve eq1486 eq152359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq152563 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95670 y
       have i₂ := eq152359
       grind)
    | exact superpose eq152359 eq95670
    | exact resolve eq95670 eq152359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95670 eq152359
  have eq152959 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97114 x
       have i₂ := eq152563
       grind)
    | exact superpose eq152563 eq97114
    | exact resolve eq97114 eq152563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97114 eq152563
  have eq152972 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq152959
  have eq202706 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152972
       grind)
    | exact superpose eq152972 eq16
    | exact resolve eq16 eq152972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152972
  have eq202966 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq202706
       have i₂ := eq111163
       grind)
    | exact superpose eq111163 eq202706
    | exact resolve eq202706 eq111163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202706
  have eq202967 : (σ x) = (σ y) := by grind
  clear eq202966
  have eq202991 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202967
       grind)
    | exact superpose eq202967 eq16
    | exact resolve eq16 eq202967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202994 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq152460
       have i₂ := eq202967
       grind)
    | exact superpose eq202967 eq152460
    | (have r₁ := eq152460
       have r₂ := eq202967
       grind)
    | exact resolve eq152460 eq202967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152460 eq202967
  have eq203132 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq202994
  have eq203191 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq202991
       have i₂ := eq111163
       grind)
    | exact superpose eq111163 eq202991
    | exact resolve eq202991 eq111163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111163 eq202991
  have eq204248 : False := by grind
  exact eq204248

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq191 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq249 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3244 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq380
    | exact resolve eq380 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq3879 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq383 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq383
    | exact resolve eq383 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq4461 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq191
    | (have j0 := eq191 y
       grind)
    | exact resolve eq191 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq191
  have eq4476 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4461
  have eq4479 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4476
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq4476
    | exact resolve eq4476 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4476
  have eq4500 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4479
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4479 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq4533 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4500 eq89
    | exact resolve eq89 eq4500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq14359 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4500 eq105
    | exact resolve eq105 eq4500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq19741 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3879 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq3879
    | exact resolve eq3879 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq3879
  have eq21146 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq14359
       grind)
    | exact superpose eq14359 eq16
    | exact resolve eq16 eq14359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14359
  have eq21212 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4533 eq21146
    | exact resolve eq21146 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21146
  have eq21218 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21212
       have r₂ := eq13 y y
       grind)
    | exact resolve eq21212 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21212
  have eq21219 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq21218
       grind)
    | exact superpose eq21218 eq78
    | exact resolve eq78 eq21218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq21257 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4500 eq21219
    | exact resolve eq21219 eq4500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4500 eq21219
  have eq29718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq29719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq29718
    | exact resolve eq29718 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29718
  have eq29730 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq29719
       have r₂ := eq28
       grind)
    | exact resolve eq29719 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29719
  have eq29764 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29730 eq3244
    | exact resolve eq3244 eq29730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32041 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29764 eq29730
    | exact resolve eq29730 eq29764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29730 eq29764
  have eq32080 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq32041
  have eq32116 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32080 eq56
    | exact resolve eq56 eq32080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32080
  have eq32135 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq32116
  have eq32168 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32135 eq4533
    | exact resolve eq4533 eq32135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533 eq32135
  have eq32240 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32168
       have i₂ := eq21218
       grind)
    | exact superpose eq21218 eq32168
    | exact resolve eq32168 eq21218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21218 eq32168
  have eq32250 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq32240
    | exact resolve eq32240 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32240
  have eq32251 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq32250
  have eq32286 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3244 x y
       have i₂ := eq32251
       grind)
    | exact superpose eq32251 eq3244
    | exact resolve eq3244 eq32251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq34115 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq32251
       have i₂ := eq32286
       grind)
    | exact superpose eq32286 eq32251
    | exact resolve eq32251 eq32286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32251 eq32286
  have eq34156 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq34115
  have eq34193 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq34156
       grind)
    | exact superpose eq34156 eq56
    | exact resolve eq56 eq34156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq34156
  have eq34214 : x = (M.op y y) := by grind
  clear eq34193
  have eq34249 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21257
       have i₂ := eq34214
       grind)
    | exact superpose eq34214 eq21257
    | exact resolve eq21257 eq34214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21257
  have eq34297 : x = (M.op x y) := by
    first
    | (have i₁ := eq19741 y y
       have i₂ := eq34214
       grind)
    | exact superpose eq34214 eq19741
    | exact resolve eq19741 eq34214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19741 eq34214
  have eq34300 : x = (M.op x y) := by
    first
    | (have i₁ := eq34297
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34297
    | exact resolve eq34297 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34297
  have eq34312 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq34249
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34249
    | exact resolve eq34249 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34249
  have eq34324 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq34300 eq21
    | exact resolve eq21 eq34300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq34300
  have eq34548 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq34324
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34324
    | exact resolve eq34324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq34324
  have eq34614 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq34548 eq27
    | exact resolve eq27 eq34548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35169 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq34548 eq34312
    | exact resolve eq34312 eq34548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34312 eq34548
  have eq35205 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq35169 eq249
    | exact resolve eq249 eq35169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq35169
  have eq36883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35205 eq34614
    | exact resolve eq34614 eq35205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34614 eq35205
  have eq36884 : False := by grind
  exact eq36884

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq48 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq81 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq48
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq119 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq110 (τ X0)
       grind)
    | exact superpose eq110 eq38
    | exact resolve eq38 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq110 (τ X0)
       grind)
    | exact superpose eq110 eq18
    | exact resolve eq18 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq121 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq119
    | exact resolve eq119 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq121 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq121
    | exact resolve eq121 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq121
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq130 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq130
    | exact resolve eq130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq24 X1 X1 X0 X2
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37
  have eq287 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq480 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq81 (τ X0) (τ X0)
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq81
    | exact resolve eq81 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq122 (M.op X0 X0)
       grind)
    | exact superpose eq122 eq480
    | exact resolve eq480 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq480
  have eq530 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq521
  have eq543 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X0)
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq11
    | exact resolve eq11 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq558 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq543
    | exact resolve eq543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq742 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq558 X0
       grind)
    | exact superpose eq558 eq79
    | exact resolve eq79 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq746 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq742 (σ X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq742
    | exact resolve eq742 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq908 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq287
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq287
    | exact resolve eq287 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq909 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq908
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq908
    | exact resolve eq908 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq910 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq909
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq909
    | exact resolve eq909 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq911 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq910
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq910
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq910 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq912 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq911
  have eq1303 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq206 X0 X1 X2 X3
       have i₂ := eq558 X1
       grind)
    | exact superpose eq558 eq206
    | exact resolve eq206 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1311 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op X2 (k (M.op X0 X0) X0))) (M.op X0 X0)) := by
    intro X0 X1 X2
    grind
  have eq1342 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1303 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq1303
    | exact resolve eq1303 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1311 X0 X1 X2
       have i₂ := eq558 X0
       grind)
    | exact superpose eq558 eq1311
    | exact resolve eq1311 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1400 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1342 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq1342
    | exact resolve eq1342 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2651 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X0 X1 X2
       have i₂ := eq558 (M.op X0 X1)
       grind)
    | exact superpose eq558 eq151
    | exact resolve eq151 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq2696 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2651 (M.op X3 (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1303 X0 X1 X2 X3
       grind)
    | exact superpose eq1303 eq2651
    | exact resolve eq2651 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq2698 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X5 (M.op X2 (M.op X3 (M.op X1 X4)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2651 (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq190 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq190 eq2651
    | exact resolve eq2651 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq2852 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X5 (M.op X2 (M.op X3 (M.op X1 X4)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2698 X0 X1 X2 X3 X4 X5
       have i₂ := eq1400 X1 X0
       grind)
    | exact superpose eq1400 eq2698
    | exact resolve eq2698 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2853 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X0) X0) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    grind
  clear eq2696
  have eq2895 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2853 X0 X1 X2 X3 X4
       have i₂ := eq558 X0
       grind)
    | exact superpose eq558 eq2853
    | exact resolve eq2853 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq2853
  have eq3631 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X1 X2
       have i₂ := eq1400 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq1400 eq182
    | exact resolve eq182 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq11786 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op X5 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X4))))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2651 (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0) X2
       have i₂ := eq2895 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq2895 eq2651
    | exact resolve eq2651 eq2895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq2895
  have eq17808 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X3 X1)) = (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X0 (M.op (M.op X1 X1) X2))))) (M.op X3 X1)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2852 X3 X1 X5 X6 (M.op (M.op (M.op X1 X1) X2) (M.op X0 (M.op (M.op X1 X1) X2))) X4
       have i₂ := eq3631 X1 X0 X2
       grind)
    | exact superpose eq3631 eq2852
    | exact resolve eq2852 eq3631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852 eq3631
  have eq41779 : (M.op y y) = (τ (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq10
    | exact resolve eq10 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq41835 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41779
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41779
    | exact resolve eq41779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41779
  have eq41836 : (σ (M.op y y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq41835
  have eq540470 : (M.op y y) = (τ (σ (M.op x x))) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq41836
       grind)
    | exact superpose eq41836 eq10
    | exact resolve eq10 eq41836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41836
  have eq540873 : (M.op y y) = (M.op x x) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq540470
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq540470
    | exact resolve eq540470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540470
  have eq540874 : x = (M.op y y) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq540873
  have eq541162 : y = (M.op y x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq25 y
       have i₂ := eq540874
       grind)
    | exact superpose eq540874 eq25
    | exact resolve eq25 eq540874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541170 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (M.op y y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 y X0
       have i₂ := eq540874
       grind)
    | exact superpose eq540874 eq81
    | exact resolve eq81 eq540874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq540874
  have eq541901 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1400 x y
       have i₂ := eq541162
       grind)
    | exact superpose eq541162 eq1400
    | exact resolve eq1400 eq541162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541162
  have eq551667 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x x)) (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1385 y x y
       have i₂ := eq541901
       grind)
    | exact superpose eq541901 eq1385
    | exact resolve eq1385 eq541901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385 eq541901
  have eq552054 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq551667 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq551667
    | exact resolve eq551667 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551667
  have eq552164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552054
       grind)
    | exact superpose eq552054 eq16
    | exact resolve eq16 eq552054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552054
  have eq552165 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq552164
       have r₂ := eq140 x
       grind)
    | exact resolve eq552164 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552164
  have eq552172 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq541170 y
       have i₂ := eq552165
       grind)
    | exact superpose eq552165 eq541170
    | (have j0 := eq541170 x
       grind)
    | exact resolve eq541170 eq552165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541170
  have eq552177 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq25 y
       have i₂ := eq552165
       grind)
    | exact superpose eq552165 eq25
    | exact resolve eq25 eq552165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552200 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq746 y
       have i₂ := eq552165
       grind)
    | exact superpose eq552165 eq746
    | exact resolve eq746 eq552165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq552891 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq552172
       have i₂ := eq1342 x y
       grind)
    | exact superpose eq1342 eq552172
    | exact resolve eq552172 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq552172
  have eq552957 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq9 x y y
       have i₂ := eq552177
       grind)
    | exact superpose eq552177 eq9
    | exact resolve eq9 eq552177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640128 : y = (M.op y (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq552177
       have i₂ := eq552891
       grind)
    | exact superpose eq552891 eq552177
    | exact resolve eq552177 eq552891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552177 eq552891
  have eq640627 : x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq640128
       have i₂ := eq552957
       grind)
    | exact superpose eq552957 eq640128
    | exact resolve eq640128 eq552957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552957 eq640128
  have eq645506 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq640627
       grind)
    | exact superpose eq640627 eq16
    | exact resolve eq16 eq640627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640627
  have eq645521 : y = (M.op x x) := by
    first
    | (have r₁ := eq645506
       have r₂ := eq140 x
       grind)
    | exact resolve eq645506 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645506
  have eq650341 : x = (M.op x y) := by
    first
    | (have i₁ := eq25 x
       have i₂ := eq645521
       grind)
    | exact superpose eq645521 eq25
    | exact resolve eq25 eq645521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq685278 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (σ (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op (M.op (σ y) (σ y)) X4))))) (σ (M.op x y))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17808 X0 (σ y) X2 (σ (M.op x y)) X4 x x
       have i₂ := eq552200
       grind)
    | exact superpose eq552200 eq17808
    | exact resolve eq17808 eq552200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17808 eq552200
  have eq686601 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op (M.op (σ y) (σ y)) X4))))) (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq685278 X0 X1 X2 X3 X4
       have i₂ := eq650341
       grind)
    | exact superpose eq650341 eq685278
    | exact resolve eq685278 eq650341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685278
  have eq687119 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op (σ (M.op y y)) X4))))) (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq686601 X0 X1 X2 X3 X4
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq686601
    | exact resolve eq686601 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686601
  have eq687434 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op (σ (M.op x y)) X4))))) (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq687119 X0 X1 X2 X3 X4
       have i₂ := eq552165
       grind)
    | exact superpose eq552165 eq687119
    | exact resolve eq687119 eq552165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687119
  have eq687569 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op (σ x) X4))))) (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq687434 X0 X1 X2 X3 X4
       have i₂ := eq650341
       grind)
    | exact superpose eq650341 eq687434
    | exact resolve eq687434 eq650341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650341 eq687434
  have eq687660 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq687569 x x x x x
       have i₂ := eq11786 (σ x) x x x x x
       grind)
    | exact superpose eq11786 eq687569
    | exact resolve eq687569 eq11786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11786 eq687569
  have eq687686 : (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq687660
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq687660
    | exact resolve eq687660 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687660
  have eq687704 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq687686
       have i₂ := eq645521
       grind)
    | exact superpose eq645521 eq687686
    | exact resolve eq687686 eq645521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645521 eq687686
  have eq709511 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1400 (σ x) (σ y)
       have i₂ := eq687704
       grind)
    | exact superpose eq687704 eq1400
    | exact resolve eq1400 eq687704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq687704
  have eq710028 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq709511
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq709511
    | exact resolve eq709511 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq709511
  have eq710162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq710028
       have i₂ := eq552165
       grind)
    | exact superpose eq552165 eq710028
    | exact resolve eq710028 eq552165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552165 eq710028
  have eq710254 : False := by grind
  exact eq710254

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9
    | (have j1 := eq28 X0
       grind)
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq102 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq300 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq301 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq21
    | exact resolve eq21 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq323 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq300 (τ X0)
       grind)
    | exact superpose eq300 eq18
    | exact resolve eq18 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq323
    | exact resolve eq323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq406 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (τ X0)
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq69
    | exact resolve eq69 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq69
  have eq618 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq45
    | (have j1 := eq28 (σ X0)
       grind)
    | exact resolve eq45 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq45
  have eq644 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq618 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq618
    | (have j0 := eq618 X0
       grind)
    | exact resolve eq618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq650 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq644 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq644
    | (have j0 := eq644 X0
       grind)
    | exact resolve eq644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq665 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (M.op X1 (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq70 (τ X0) X1
       grind)
    | exact superpose eq70 eq18
    | (have j1 := eq70 (τ X0) X1
       grind)
    | exact resolve eq18 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq666 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (M.op X1 (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq690 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq90
    | exact resolve eq90 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq932 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq102 X0 X1 X2
       grind)
    | exact superpose eq102 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq102 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq102 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq102 X0 X1 X2
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq942 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq932 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq943 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq942 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq949 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq943 X0 X1 X2
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq943
    | (have j0 := eq943 X0 X1 X2
       grind)
    | exact resolve eq943 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq943
  have eq950 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq949 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1656 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq53
    | (have j1 := eq650 X0
       grind)
    | exact resolve eq53 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq7098 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq666 X0 x
       have i₂ := eq690 (τ X0) x
       grind)
    | exact superpose eq690 eq666
    | (have j0 := eq666 X0 x
       grind)
    | exact resolve eq666 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq690
  have eq7209 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq7098 X0
       grind)
    | exact superpose eq7098 eq10
    | (have j1 := eq7098 X0
       grind)
    | exact resolve eq10 eq7098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7098
  have eq9023 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (M.op (k (σ X0) (σ X1)) (σ X2)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq950 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq950
    | (have j0 := eq950 (σ X0) X1 X2
       grind)
    | exact resolve eq950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9052 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (k X0 (σ (M.op (τ X0) (τ X0)))) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq300 (τ X0)
       grind)
    | exact superpose eq300 eq950
    | (have j0 := eq950 X0 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact resolve eq950 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq9250 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9052 X0 X1
       have i₂ := eq324 X0
       grind)
    | exact superpose eq324 eq9052
    | (have j0 := eq9052 X0 X1
       grind)
    | exact resolve eq9052 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9052
  have eq9265 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (M.op (σ (k X0 X1)) (σ X2)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9023 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9023
    | (have j0 := eq9023 X0 X1 X2
       grind)
    | exact resolve eq9023 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9023
  have eq9332 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9250 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9250
    | (have j0 := eq9250 X0 X1
       grind)
    | exact resolve eq9250 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9250
  have eq9347 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 X1) X2)) = (M.op (σ (k X0 X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9265 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9265
    | (have j0 := eq9265 X0 X1 X2
       grind)
    | exact resolve eq9265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9265
  have eq9399 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9332 X0 X1
       have i₂ := eq324 X0
       grind)
    | exact superpose eq324 eq9332
    | (have j0 := eq9332 X0 X1
       grind)
    | exact resolve eq9332 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq9332
  have eq9496 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9399 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9399
    | exact resolve eq9399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9399
  have eq28413 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1656 X0
       have i₂ := eq9496 X0 X0
       grind)
    | exact superpose eq9496 eq1656
    | (have j1 := eq9496 X0 X0
       grind)
    | exact resolve eq1656 eq9496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq28518 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28413
  have eq164472 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7209
  have eq164481 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq164472 X0
       have j1 := eq406 X0
       grind)
    | (have r₁ := eq164472 X0
       have r₂ := eq406 X0
       grind)
    | exact resolve eq164472 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq164472
  have eq164933 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq164481 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164481
    | exact resolve eq164481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164481
  have eq165372 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq164933 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq164933
    | exact resolve eq164933 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq164933
  have eq165446 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq165372 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165372
    | exact resolve eq165372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165372
  have eq169266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq165446 (σ X0)
       grind)
    | exact superpose eq165446 eq15
    | exact resolve eq15 eq165446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169469 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq169266 X0
       have i₂ := eq165446 X0
       grind)
    | exact superpose eq165446 eq169266
    | exact resolve eq169266 eq165446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165446 eq169266
  have eq175620 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq301 (σ X0)
       have i₂ := eq169469 X0
       grind)
    | exact superpose eq169469 eq301
    | exact resolve eq301 eq169469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731711 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (M.op (σ (k X0 X1)) (σ X2)) ∨ (σ (k X0 X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9347 X0 X1 X2
       have i₂ := eq169469 X2
       grind)
    | exact superpose eq169469 eq9347
    | (have j0 := eq9347 X0 X1 X2
       grind)
    | exact resolve eq9347 eq169469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347
  have eq731740 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq731711 X0 (M.op X0 X0) x
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq731711
    | exact resolve eq731711 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq731711
  have eq734643 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq731740 x y
       grind)
    | exact superpose eq731740 eq16
    | (have j1 := eq731740 x y
       grind)
    | exact resolve eq16 eq731740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731740
  have eq738479 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq734643
       have i₂ := eq9496 y x
       grind)
    | exact superpose eq9496 eq734643
    | (have j1 := eq9496 y x
       grind)
    | exact resolve eq734643 eq9496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9496 eq734643
  have eq738486 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq738479
  have eq738672 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq738486
       grind)
    | exact superpose eq738486 eq53
    | exact resolve eq53 eq738486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq738486
  have eq741176 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq28518 x
       have i₂ := eq738672
       grind)
    | exact superpose eq738672 eq28518
    | exact resolve eq28518 eq738672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28518 eq738672
  have eq741729 : (σ x) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq741176
       have i₂ := eq169469 y
       grind)
    | exact superpose eq169469 eq741176
    | exact resolve eq741176 eq169469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741176
  have eq741730 : x = y ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq741729
  have eq741917 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq741730
       grind)
    | exact superpose eq741730 eq16
    | exact resolve eq16 eq741730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741730
  have eq741928 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq741917
       have r₂ := eq169469 x
       grind)
    | exact resolve eq741917 eq169469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169469 eq741917
  have eq743853 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175620 y
       have i₂ := eq741928
       grind)
    | exact superpose eq741928 eq175620
    | exact resolve eq175620 eq741928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175620
  have eq743886 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq741928
       grind)
    | exact superpose eq741928 eq10
    | exact resolve eq10 eq741928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741928
  have eq744664 : x = (M.op y y) := by
    first
    | (have i₁ := eq743886
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq743886
    | exact resolve eq743886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743886
  have eq747049 : x = (M.op x y) := by
    first
    | (have i₁ := eq301 y
       have i₂ := eq744664
       grind)
    | exact superpose eq744664 eq301
    | exact resolve eq301 eq744664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq744664
  have eq799306 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq743853
       grind)
    | exact superpose eq743853 eq16
    | exact resolve eq16 eq743853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743853
  have eq799850 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq799306
       have i₂ := eq747049
       grind)
    | exact superpose eq747049 eq799306
    | exact resolve eq799306 eq747049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747049 eq799306
  have eq799851 : False := by grind
  exact eq799851

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq65 X0 X2
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq81 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (M.op X0 X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq80
    | exact resolve eq80 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq80 (σ X0)
       grind)
    | exact superpose eq80 eq23
    | exact resolve eq23 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq81 (τ X0)
       grind)
    | exact superpose eq81 eq18
    | exact resolve eq18 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1 (M.op X0 X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq73
    | exact resolve eq73 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq595 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq640 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X2 (M.op X0 X1) X1
       have i₂ := eq65 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq65 eq62
    | exact resolve eq62 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq62 X1 X1 X0 X2
       grind)
    | exact superpose eq62 eq73
    | exact resolve eq73 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq672 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq641 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq641
    | exact resolve eq641 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq672 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq672
    | exact resolve eq672 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq731 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 X2
       have i₂ := eq703 X0 X2
       grind)
    | exact superpose eq703 eq71
    | exact resolve eq71 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq732 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X0 X3) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq703 (M.op X0 X3) X2
       grind)
    | exact superpose eq703 eq62
    | exact resolve eq62 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq798 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X1) X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq731 X1 X3 X0
       grind)
    | exact superpose eq731 eq9
    | exact resolve eq9 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq672 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq731 X1 X2 X0
       grind)
    | exact superpose eq731 eq672
    | exact resolve eq672 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq804 X0 X1 X2
       have i₂ := eq703 X1 X2
       grind)
    | exact superpose eq703 eq804
    | exact resolve eq804 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq811 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq798 X0 X1 X2 X3
       have i₂ := eq703 X1 X3
       grind)
    | exact superpose eq703 eq798
    | exact resolve eq798 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq798
  have eq934 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq640 X0 X1 X2
       have i₂ := eq806 X0 X1 X0
       grind)
    | exact superpose eq806 eq640
    | exact resolve eq640 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq941 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op X0 X0) X3)) = (M.op X0 (M.op (M.op X0 X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq934 (M.op X0 X0) X3 (M.op x (M.op X0 x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq934
    | exact resolve eq934 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq934 (M.op X1 X0) (M.op X0 (M.op X2 X0)) X2
       have i₂ := eq731 X0 X1 X2
       grind)
    | exact superpose eq731 eq934
    | exact resolve eq934 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq934 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq934 X0 X1 X2
       grind)
    | (have i₁ := eq934 X1 (M.op X0 X1) X2
       have i₂ := eq934 X0 X1 X2
       grind)
    | exact superpose eq934 eq934
    | exact resolve eq934 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq958 X0 X1 X2 X3
       have i₂ := eq731 X0 X1 X1
       grind)
    | exact superpose eq731 eq958
    | exact resolve eq958 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1022 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq957 X0 X1 X2 X3
       have i₂ := eq125 (M.op X0 X1) X1
       grind)
    | exact superpose eq125 eq957
    | exact resolve eq957 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1031 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1022 X0 X1 X2 X3
       have i₂ := eq806 X0 X1 X0
       grind)
    | exact superpose eq806 eq1022
    | exact resolve eq1022 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1531 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq811 X0 X0 (M.op x (M.op X0 x)) X1
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq811
    | exact resolve eq811 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq2020 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 (M.op X0 X1)
       have i₂ := eq934 X0 X1 X0
       grind)
    | (have i₁ := eq941 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq934 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq934 eq941
    | exact resolve eq941 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2024 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq941 X0 (M.op (M.op X0 x) (M.op X2 (M.op X0 x)))
       have i₂ := eq732 X0 X0 X2 x
       grind)
    | exact superpose eq732 eq941
    | exact resolve eq941 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq2132 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2024 X0 X1 X2
       have i₂ := eq125 (M.op X0 (M.op X1 X2)) (M.op X1 X2)
       grind)
    | exact superpose eq125 eq2024
    | exact resolve eq2024 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2136 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2020 X0 X1
       have i₂ := eq731 X0 X1 X1
       grind)
    | exact superpose eq731 eq2020
    | exact resolve eq2020 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq2020
  have eq2150 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2132 X0 X1 X2
       have i₂ := eq806 X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq806 eq2132
    | exact resolve eq2132 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq2132
  have eq2174 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2136 X2 X1
       have i₂ := eq934 X1 X2 X0
       grind)
    | (have i₁ := eq2136 (M.op X2 X0) X0
       have i₂ := eq934 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq934 eq2136
    | exact resolve eq2136 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136
  have eq2971 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op X4 (M.op X5 (M.op X1 (M.op X2 (M.op X0 X3))))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1021 X1 (M.op X3 (M.op X0 (M.op X1 X2))) X2 X3
       have i₂ := eq641 X0 X1 X2 X3
       grind)
    | exact superpose eq641 eq1021
    | exact resolve eq1021 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq3141 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op X4 (M.op X5 (M.op X1 (M.op X2 (M.op X0 X3))))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2971 X0 X1 X2 X3 X4 X5
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq2971
    | exact resolve eq2971 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq3623 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq579
    | (have j0 := eq579 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq579 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3627 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq579 (M.op X0 X0) X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq579
    | (have j0 := eq579 (M.op X0 X0) X0
       grind)
    | exact resolve eq579 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3652 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq579 X0 X1
       grind)
    | exact superpose eq579 eq10
    | (have j1 := eq579 X0 X1
       grind)
    | exact resolve eq10 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3654 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 X1))) = (k (σ X2) (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 X1)
       have i₂ := eq579 X0 X1
       grind)
    | exact superpose eq579 eq15
    | (have j1 := eq579 X0 X1
       grind)
    | exact resolve eq15 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq7607 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq732 X0 X1 X2 X3
       have i₂ := eq2150 X2 X0 X3
       grind)
    | exact superpose eq2150 eq732
    | exact resolve eq732 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq2150
  have eq9117 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7607 (M.op X0 X1) X3 X1 (M.op X1 X2)
       have i₂ := eq7607 X1 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq7607 eq7607
    | exact resolve eq7607 eq7607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7607
  have eq9301 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9117 X0 X1 X2 X3
       have i₂ := eq2174 X0 X1 X2
       grind)
    | exact superpose eq2174 eq9117
    | exact resolve eq9117 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq9117
  have eq9589 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X0) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq934 (M.op X3 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 X2)) X2
       have i₂ := eq9301 X0 X1 X2 X3
       grind)
    | exact superpose eq9301 eq934
    | exact resolve eq934 eq9301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq9675 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9589 X0 X1 X2 X3 X4
       have i₂ := eq1031 X0 X1 (M.op X4 X0) X0
       grind)
    | exact superpose eq1031 eq9589
    | exact resolve eq9589 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq9589
  have eq10339 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X1 (M.op X2 (M.op X0 X3)))))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq9675 (M.op X3 (M.op X0 (M.op X1 X2))) X1 X2 X3 X4
       have i₂ := eq641 X0 X1 X2 X3
       grind)
    | exact superpose eq641 eq9675
    | exact resolve eq9675 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq9675
  have eq10745 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X1 (M.op X2 (M.op X0 X3)))))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq10339 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq10339
    | exact resolve eq10339 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10339
  have eq13718 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X0 X1))))) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3141 X1 X4 X5 (M.op X1 (M.op X0 X1)) X2 X3
       have i₂ := eq1531 X1 X0
       grind)
    | exact superpose eq1531 eq3141
    | exact resolve eq3141 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq18627 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 x
       have i₂ := eq595 (τ x) x
       grind)
    | exact superpose eq595 eq88
    | (have j1 := eq595 (τ X0) X0
       grind)
    | exact resolve eq88 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq595
  have eq18643 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq18627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627
  have eq18657 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18643 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18643
    | (have j0 := eq18643 X0
       grind)
    | exact resolve eq18643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18643
  have eq19315 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (k (σ X0) (σ X0))
       have i₂ := eq18657 (σ X0)
       grind)
    | exact superpose eq18657 eq29
    | (have j1 := eq18657 (σ X0)
       grind)
    | exact resolve eq29 eq18657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18657
  have eq19335 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19315 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq19315
    | (have j0 := eq19315 X0
       grind)
    | exact resolve eq19315 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19315
  have eq19351 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19335 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19335
    | (have j0 := eq19335 X0
       grind)
    | exact resolve eq19335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19335
  have eq19361 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19351 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19351
    | (have j0 := eq19351 X0
       grind)
    | exact resolve eq19351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19351
  have eq19378 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (k (σ X0) (σ X0))
       have i₂ := eq19361 (σ X0)
       grind)
    | exact superpose eq19361 eq29
    | (have j1 := eq19361 (σ X0)
       grind)
    | exact resolve eq29 eq19361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19361
  have eq19398 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (k (τ (σ X0)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19378 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq19378
    | (have j0 := eq19378 X0
       grind)
    | exact resolve eq19378 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19378
  have eq19414 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19398 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19398
    | (have j0 := eq19398 X0
       grind)
    | exact resolve eq19398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19398
  have eq68538 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 (M.op X0 X1)))))) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq10745 X1 X5 X6 (M.op X1 (M.op X0 X1)) X2 X3 X4
       have i₂ := eq1531 X1 X0
       grind)
    | exact superpose eq1531 eq10745
    | exact resolve eq10745 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq78955 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 (σ X0)
       have i₂ := eq3654 X0 X0 X0
       grind)
    | exact superpose eq3654 eq81
    | (have j1 := eq3654 X0 X0 x
       grind)
    | exact resolve eq81 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq3654
  have eq78958 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78955
  have eq78961 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq19414 eq78958
    | (have j0 := eq78958 X0
       have j1 := eq19414 X0
       grind)
    | exact resolve eq78958 eq19414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19414 eq78958
  have eq79000 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq78961 (τ X0)
       grind)
    | exact superpose eq78961 eq19
    | (have j1 := eq78961 (τ X0)
       grind)
    | exact resolve eq19 eq78961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq79005 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq78961 X0
       grind)
    | exact superpose eq78961 eq10
    | (have j1 := eq78961 X0
       grind)
    | exact resolve eq10 eq78961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79035 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq79000 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79000
    | (have j0 := eq79000 X0
       grind)
    | exact resolve eq79000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79000
  have eq79055 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79035 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79035
    | (have j0 := eq79035 X0
       grind)
    | exact resolve eq79035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79035
  have eq79116 : ∀ X0 : G, (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) = (k (k X0 X0) (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79005 (k X0 X0)
       have i₂ := eq78961 X0
       grind)
    | exact superpose eq78961 eq79005
    | (have j0 := eq79005 X0
       have j1 := eq78961 X0
       grind)
    | exact resolve eq79005 eq78961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78961 eq79005
  have eq79161 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79116 X0
       have i₂ := eq934 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq934 eq79116
    | (have j0 := eq79116 X0
       grind)
    | exact resolve eq79116 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79116
  have eq79168 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79161 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq79161
    | (have j0 := eq79161 X0
       grind)
    | exact resolve eq79161 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79161
  have eq79170 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79168 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79168
    | (have j0 := eq79168 X0
       grind)
    | exact resolve eq79168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79168
  have eq79172 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79170 X0
       have i₂ := eq934 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq934 eq79170
    | (have j0 := eq79170 X0
       grind)
    | exact resolve eq79170 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq79170
  have eq79173 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79172 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq79172
    | (have j0 := eq79172 X0
       grind)
    | exact resolve eq79172 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79172
  have eq79174 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79173
  have eq79182 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (τ X0) X0 (k (τ X0) (τ X0))
       have i₂ := eq79174 (τ X0)
       grind)
    | exact superpose eq79174 eq28
    | (have j1 := eq79174 (τ X0)
       grind)
    | exact resolve eq28 eq79174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq79203 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq79182 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq79182
    | (have j0 := eq79182 X0
       grind)
    | exact resolve eq79182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq79182
  have eq79213 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq79203 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79203
    | (have j0 := eq79203 X0
       grind)
    | exact resolve eq79203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79203
  have eq79219 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq79213 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79213
    | (have j0 := eq79213 X0
       grind)
    | exact resolve eq79213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79213
  have eq79224 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq79055 eq79219
    | (have j0 := eq79219 X0
       have j1 := eq79055 X0
       grind)
    | exact resolve eq79219 eq79055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79055 eq79219
  have eq79671 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq125 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq3627 X0
       grind)
    | exact superpose eq3627 eq125
    | (have j1 := eq3627 X0
       grind)
    | exact resolve eq125 eq3627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79852 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3627 eq79671
    | (have j0 := eq79671 X0
       have j1 := eq3627 X0
       grind)
    | exact resolve eq79671 eq3627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627 eq79671
  have eq79853 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79852
  have eq79921 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq79853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79853
  have eq80700 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq79921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79921
  have eq81569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3623 x y
       grind)
    | exact superpose eq3623 eq16
    | (have j1 := eq3623 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3623 x y
       grind)
    | exact resolve eq16 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81570 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq3623 X0 X0
       grind)
    | exact superpose eq3623 eq63
    | (have j1 := eq3623 X0 X0
       grind)
    | exact resolve eq63 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq3623
  have eq81775 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq81570 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81570
  have eq81776 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq81569
  have eq82874 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq80700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80700
  have eq330801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq125 (σ y) (σ y)
       have i₂ := eq81776
       grind)
    | exact superpose eq81776 eq125
    | exact resolve eq125 eq81776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81776
  have eq331087 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq330801
  have eq331152 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq331087
  have eq331288 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq331152
       grind)
    | exact superpose eq331152 eq16
    | exact resolve eq16 eq331152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331291 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq125 (σ y) (σ x)
       have i₂ := eq331152
       grind)
    | exact superpose eq331152 eq125
    | exact resolve eq125 eq331152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331641 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq331152 eq331291
    | exact resolve eq331291 eq331152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331152 eq331291
  have eq332054 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84 y
       have i₂ := eq331641
       grind)
    | exact superpose eq331641 eq84
    | exact resolve eq84 eq331641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332207 : ∀ X0 X1 X2 X3 X4 : G, (σ y) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X4 (σ x)))))) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10745 (σ y) X1 X2 (σ y) X4 x x
       have i₂ := eq331641
       grind)
    | exact superpose eq331641 eq10745
    | exact resolve eq10745 eq331641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10745
  have eq332440 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq332207 x x x x x
       have i₂ := eq13718 x (σ x) x x x x
       grind)
    | exact superpose eq13718 eq332207
    | exact resolve eq332207 eq13718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332207
  have eq332464 : y = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq332054
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq332054
    | exact resolve eq332054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332054
  have eq332490 : y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq332464
       have r₂ := eq13 x y
       grind)
    | exact resolve eq332464 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332464
  have eq332504 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq332490
       grind)
    | exact superpose eq332490 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq332490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332490
  have eq332505 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq332504
  have eq332511 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq332505 eq331288
    | exact resolve eq331288 eq332505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331288 eq332505
  have eq335091 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3652 x x
       have i₂ := eq332440
       grind)
    | exact superpose eq332440 eq3652
    | exact resolve eq3652 eq332440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq335435 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq335091
  have eq335522 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq335435
       have r₂ := eq332511
       grind)
    | exact resolve eq335435 eq332511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335435
  have eq335564 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq335522
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq335522
    | exact resolve eq335522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335522
  have eq335594 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79174 x
       have i₂ := eq335564
       grind)
    | exact superpose eq335564 eq79174
    | (have j0 := eq79174 x
       grind)
    | exact resolve eq79174 eq335564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79174 eq335564
  have eq335631 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq332440 eq335594
    | exact resolve eq335594 eq332440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332440 eq335594
  have eq335636 : x = (k y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq335631
       have r₂ := eq332511
       grind)
    | exact resolve eq335631 eq332511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335631
  have eq335674 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq335636
       grind)
    | exact superpose eq335636 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq335636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335636
  have eq335675 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq335674
  have eq335729 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82874 y
       have i₂ := eq335675
       grind)
    | exact superpose eq335675 eq82874
    | exact resolve eq82874 eq335675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335675
  have eq336026 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq335729
  have eq336116 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq331641 eq336026
    | exact resolve eq336026 eq331641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331641 eq336026
  have eq336129 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq336116
       have r₂ := eq332511
       grind)
    | exact resolve eq336116 eq332511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332511 eq336116
  have eq336192 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq672 y y
       have i₂ := eq336129
       grind)
    | exact superpose eq336129 eq672
    | exact resolve eq672 eq336129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq336129
  have eq336474 : x = (M.op x y) := by grind
  clear eq336192
  have eq336595 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq336474
       grind)
    | exact superpose eq336474 eq16
    | exact resolve eq16 eq336474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336597 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq125 y x
       have i₂ := eq336474
       grind)
    | exact superpose eq336474 eq125
    | exact resolve eq125 eq336474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq336941 : x = (M.op y y) := by
    first
    | (have i₁ := eq336597
       have i₂ := eq336474
       grind)
    | exact superpose eq336474 eq336597
    | exact resolve eq336597 eq336474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336597
  have eq337852 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq79224 y
       have i₂ := eq336941
       grind)
    | exact superpose eq336941 eq79224
    | exact resolve eq79224 eq336941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79224
  have eq338102 : ∀ X0 X1 X2 X3 X4 : G, y = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X4 x))))) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq68538 y y X2 X3 X4 x x
       have i₂ := eq336941
       grind)
    | exact superpose eq336941 eq68538
    | exact resolve eq68538 eq336941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68538 eq336941
  have eq338163 : y = (M.op x x) := by
    first
    | (have i₁ := eq338102 x x x x x
       have i₂ := eq13718 x x x x x x
       grind)
    | exact superpose eq13718 eq338102
    | exact resolve eq338102 eq13718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13718 eq338102
  have eq338655 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq81775 x
       have i₂ := eq338163
       grind)
    | exact superpose eq338163 eq81775
    | (have j0 := eq81775 x
       grind)
    | exact resolve eq81775 eq338163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81775 eq338163
  have eq339024 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq338655
       have r₂ := eq336595
       grind)
    | exact resolve eq338655 eq336595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338655
  have eq377068 : x = (k (τ (σ x)) x) ∨ x = y := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq339024
       grind)
    | exact superpose eq339024 eq84
    | exact resolve eq84 eq339024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq339024
  have eq377505 : x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq377068
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq377068
    | exact resolve eq377068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377068
  have eq377522 : x = y ∨ x = y := by
    first
    | exact superpose eq377505 eq337852
    | exact resolve eq337852 eq377505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337852 eq377505
  have eq377558 : x = y := by grind
  clear eq377522
  have eq377572 : x = (M.op x x) := by
    first
    | (have i₁ := eq336474
       have i₂ := eq377558
       grind)
    | exact superpose eq377558 eq336474
    | exact resolve eq336474 eq377558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336474
  have eq377573 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq336595
       have i₂ := eq377558
       grind)
    | exact superpose eq377558 eq336595
    | exact resolve eq336595 eq377558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336595 eq377558
  have eq377639 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82874 x
       have i₂ := eq377572
       grind)
    | exact superpose eq377572 eq82874
    | exact resolve eq82874 eq377572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82874 eq377572
  have eq377944 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq377639
  have eq378036 : False := by grind
  exact eq378036

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq9
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq63 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq83 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq30
    | exact resolve eq30 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq92 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X2 (M.op X0 X1) X1
       have i₂ := eq36 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq36 eq33
    | exact resolve eq33 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq33 X1 X4 X0 X2
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq36
    | (have j1 := eq65 X0 X0
       grind)
    | exact resolve eq36 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq174 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq242 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq33 X1 X1 X0 X2
       grind)
    | exact superpose eq33 eq43
    | exact resolve eq43 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq322 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq242 X2 X0 (M.op X0 X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq242
    | exact resolve eq242 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq242 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq34 (M.op X0 X1)
       grind)
    | exact superpose eq34 eq242
    | exact resolve eq242 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq360 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq336 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq336
    | exact resolve eq336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq336
    | exact resolve eq336 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X3 X1)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq336 (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq33 X1 X3 X0 X2
       grind)
    | exact superpose eq33 eq336
    | exact resolve eq336 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq360 X0 X1 X2
       have i₂ := eq361 (M.op X0 X2) X1
       grind)
    | exact superpose eq361 eq360
    | exact resolve eq360 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq587 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X1 X0)
       have i₂ := eq361 X0 X1
       grind)
    | exact superpose eq361 eq34
    | exact resolve eq34 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq384 X1 X0 X0
       grind)
    | exact superpose eq384 eq587
    | exact resolve eq587 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq587
  have eq987 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 X1 X0 X1 X0 X2
       have i₂ := eq610 X1 X0
       grind)
    | exact superpose eq610 eq113
    | exact resolve eq113 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1061 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq987 X0 X1 X2
       have i₂ := eq361 X0 X2
       grind)
    | exact superpose eq361 eq987
    | exact resolve eq987 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1144 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X2 X1 X1
       have i₂ := eq1061 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq1061 eq33
    | exact resolve eq33 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1061
  have eq2042 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2096 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2042 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2042
    | (have j0 := eq2042 X0 X1
       grind)
    | exact resolve eq2042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2807 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq167 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq167
    | (have j0 := eq167 (σ X0) (σ X1)
       grind)
    | exact resolve eq167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq155
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq155 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq3242 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq3241
  have eq15213 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq174
    | (have j0 := eq174 (τ X0) X1
       grind)
    | exact resolve eq174 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq15331 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15213 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15213
    | (have j0 := eq15213 X0 X1
       grind)
    | exact resolve eq15213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15213
  have eq15352 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15331 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15331
    | (have j0 := eq15331 X0 X1
       grind)
    | exact resolve eq15331 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15331
  have eq15427 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq336 (k X0 X0) X0
       have i₂ := eq15352 X0 (k X0 X0)
       grind)
    | exact superpose eq15352 eq336
    | (have j1 := eq15352 X0 x
       grind)
    | exact resolve eq336 eq15352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15352
  have eq15646 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (k X0 X0) (k X0 X0)
       have i₂ := eq15427 X0
       grind)
    | exact superpose eq15427 eq36
    | (have j1 := eq15427 X0
       grind)
    | exact resolve eq36 eq15427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427
  have eq16007 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq15646 (σ X0)
       grind)
    | exact superpose eq15646 eq15
    | (have j1 := eq15646 (σ X0)
       grind)
    | exact resolve eq15 eq15646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq33128 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op (M.op X4 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq109 X3 X1 X4
       have i₂ := eq362 X0 X1 X2 X3
       grind)
    | exact superpose eq362 eq109
    | exact resolve eq109 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq362
  have eq38654 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33128 X0 X1 (M.op X0 X1) X2 X3
       have i₂ := eq610 X1 X0
       grind)
    | exact superpose eq610 eq33128
    | exact resolve eq33128 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq33128
  have eq71310 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3242
       grind)
    | exact superpose eq3242 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3242
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3242
       grind)
    | exact resolve eq13 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq71450 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq71310
  have eq71451 : x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq71450
  have eq96361 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (σ X0)
       have i₂ := eq16007 X0
       grind)
    | exact superpose eq16007 eq44
    | (have j1 := eq16007 X0
       grind)
    | exact resolve eq44 eq16007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96541 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq16007 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16007
  have eq96614 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96361 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq96361
    | (have j0 := eq96361 X0
       grind)
    | exact resolve eq96361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96361
  have eq96636 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq96614 X0
       have j1 := eq96541 X0
       grind)
    | (have r₁ := eq96614 X0
       have r₂ := eq96541 X0
       grind)
    | exact resolve eq96614 eq96541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96541 eq96614
  have eq96653 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq96636 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96636
    | exact resolve eq96636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96702 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq96636 X0
       grind)
    | exact superpose eq96636 eq92
    | exact resolve eq92 eq96636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96725 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq96636 X0
       grind)
    | exact superpose eq96636 eq34
    | exact resolve eq34 eq96636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq96730 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq44 (σ X0)
       have i₂ := eq96636 X0
       grind)
    | exact superpose eq96636 eq44
    | exact resolve eq44 eq96636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq97018 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq96730 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq96730
    | exact resolve eq96730 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96730
  have eq97038 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq96702 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq96702
    | exact resolve eq96702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96702
  have eq97068 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq96653 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq96653
    | exact resolve eq96653 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96653
  have eq97122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq97068 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97068
    | exact resolve eq97068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97068
  have eq98906 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq96636 (k X0 (k X0 X0))
       have i₂ := eq97018 X0
       grind)
    | exact superpose eq97018 eq96636
    | exact resolve eq96636 eq97018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97018
  have eq98919 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq98906 X0
       have i₂ := eq97122 (k X0 (k X0 X0))
       grind)
    | exact superpose eq97122 eq98906
    | exact resolve eq98906 eq97122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98906
  have eq99013 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98919 X0
       have i₂ := eq97038 X0
       grind)
    | exact superpose eq97038 eq98919
    | exact resolve eq98919 eq97038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97038 eq98919
  have eq100727 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq96725 X0
       have i₂ := eq97122 X0
       grind)
    | exact superpose eq97122 eq96725
    | exact resolve eq96725 eq97122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96725
  have eq104002 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq336 (σ X0) (σ X0)
       have i₂ := eq99013 X0
       grind)
    | exact superpose eq99013 eq336
    | exact resolve eq336 eq99013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq104031 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1144 (σ X0) X1 (σ X0)
       have i₂ := eq99013 X0
       grind)
    | exact superpose eq99013 eq1144
    | exact resolve eq1144 eq99013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq99013
  have eq104525 : ∀ X0 X1 X2 : G, (σ (M.op X1 X2)) = (M.op (σ (M.op X1 X2)) (σ (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100727 (M.op X1 X2)
       have i₂ := eq38654 X1 X2 X1 X0
       grind)
    | (have i₁ := eq100727 (M.op X1 X1)
       have i₂ := eq38654 X0 X1 X1 X1
       grind)
    | exact superpose eq38654 eq100727
    | exact resolve eq100727 eq38654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38654 eq100727
  have eq127460 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2807 (τ X0) (τ X1)
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq2807
    | (have j0 := eq2807 (τ X0) (τ X1)
       grind)
    | exact resolve eq2807 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2807
  have eq127631 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq127460 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq127460
    | (have j0 := eq127460 X0 X1
       grind)
    | exact resolve eq127460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127460
  have eq127712 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq127631 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127631
    | (have j0 := eq127631 X0 X1
       grind)
    | exact resolve eq127631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127631
  have eq127785 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq127712 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq127712
    | (have j0 := eq127712 X0 X1
       grind)
    | exact resolve eq127712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127712
  have eq127850 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq127785 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127785
    | (have j0 := eq127785 X0 X1
       grind)
    | exact resolve eq127785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127785
  have eq127908 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127850 X0 X1
       have i₂ := eq96636 (σ (τ X1))
       grind)
    | exact superpose eq96636 eq127850
    | (have j0 := eq127850 X0 X1
       grind)
    | exact resolve eq127850 eq96636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127850
  have eq127956 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127908 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq127908
    | (have j0 := eq127908 X0 X1
       grind)
    | exact resolve eq127908 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127908
  have eq127997 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127956 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq127956
    | (have j0 := eq127956 X0 X1
       grind)
    | exact resolve eq127956 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq127956
  have eq128032 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127997 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq127997
    | (have j0 := eq127997 X0 X1
       grind)
    | exact resolve eq127997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127997
  have eq128057 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128032 X0 X1
       have i₂ := eq97122 X1
       grind)
    | exact superpose eq97122 eq128032
    | (have j0 := eq128032 X0 X1
       grind)
    | exact resolve eq128032 eq97122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128032
  have eq128073 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128057 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq128057
    | (have j0 := eq128057 X0 X1
       grind)
    | exact resolve eq128057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128057
  have eq340242 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X1) (M.op X0 X1))) (σ (M.op X0 X1))) = (M.op (σ (M.op (M.op X2 X0) (M.op X0 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104031 (M.op X1 X2) (σ (M.op (M.op X0 X1) (M.op X1 X2)))
       have i₂ := eq104525 X0 X1 X2
       grind)
    | exact superpose eq104525 eq104031
    | exact resolve eq104031 eq104525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104031 eq104525
  have eq340610 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ (M.op (M.op X2 X0) (M.op X0 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq340242 X0 X1 X2
       have i₂ := eq104002 (M.op X0 X1)
       grind)
    | exact superpose eq104002 eq340242
    | exact resolve eq340242 eq104002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104002 eq340242
  have eq341123 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X0 X1))) = (M.op (σ (M.op (M.op X2 X0) (M.op X0 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq340610 X0 X1 X2
       have i₂ := eq361 X1 X0
       grind)
    | exact superpose eq361 eq340610
    | exact resolve eq340610 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq340610
  have eq2744640 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128073 x y
       have i₂ := eq71451
       grind)
    | exact superpose eq71451 eq128073
    | (have j0 := eq128073 x y
       grind)
    | exact resolve eq128073 eq71451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71451 eq128073
  have eq2744653 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2744640
  have eq2744654 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2744653
  have eq2744679 : (σ x) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2744654
       have i₂ := eq96636 y
       grind)
    | exact superpose eq96636 eq2744654
    | exact resolve eq2744654 eq96636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744654
  have eq2744686 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2744679
       have i₂ := eq97122 y
       grind)
    | exact superpose eq97122 eq2744679
    | exact resolve eq2744679 eq97122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744679
  have eq2744687 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2744686
  have eq2744699 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2744687
       grind)
    | exact superpose eq2744687 eq16
    | exact resolve eq16 eq2744687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2744791 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2744687
       grind)
    | exact superpose eq2744687 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2744687
       grind)
    | exact resolve eq13 eq2744687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744687
  have eq2745294 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2744791
  have eq2745553 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2745294
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2745294
    | exact resolve eq2745294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745294
  have eq2745778 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2745553
       have i₂ := eq96636 y
       grind)
    | exact superpose eq96636 eq2745553
    | exact resolve eq2745553 eq96636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96636 eq2745553
  have eq2745899 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2745778
       have i₂ := eq97122 y
       grind)
    | exact superpose eq97122 eq2745778
    | exact resolve eq2745778 eq97122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97122 eq2745778
  have eq2745900 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2745899
  have eq2751707 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2096 y x
       have i₂ := eq2745900
       grind)
    | exact superpose eq2745900 eq2096
    | (have j0 := eq2096 y x
       grind)
    | exact resolve eq2096 eq2745900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096 eq2745900
  have eq2752333 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2751707
  have eq2752728 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2752333
       have r₂ := eq2744699
       grind)
    | exact resolve eq2752333 eq2744699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752333
  have eq2754249 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2744699
       have i₂ := eq2752728
       grind)
    | exact superpose eq2752728 eq2744699
    | exact resolve eq2744699 eq2752728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744699 eq2752728
  have eq2754754 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2754249
  have eq2754755 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2754754
  have eq2755078 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2754755
       grind)
    | exact superpose eq2754755 eq10
    | exact resolve eq10 eq2754755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754755
  have eq2756170 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2755078
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2755078
    | exact resolve eq2755078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755078
  have eq2756171 : x = (M.op y y) := by grind
  clear eq2756170
  have eq2764660 : y = (M.op x x) := by
    first
    | (have i₁ := eq36 y y
       have i₂ := eq2756171
       grind)
    | exact superpose eq2756171 eq36
    | exact resolve eq36 eq2756171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2764678 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq322 y x y
       have i₂ := eq2756171
       grind)
    | exact superpose eq2756171 eq322
    | exact resolve eq322 eq2756171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq2756171
  have eq2773531 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op X0 x) y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq341123 x x x
       have i₂ := eq2764660
       grind)
    | exact superpose eq2764660 eq341123
    | exact resolve eq341123 eq2764660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341123 eq2764660
  have eq2773645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2773531 x
       have i₂ := eq2764678 x
       grind)
    | exact superpose eq2764678 eq2773531
    | exact resolve eq2773531 eq2764678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764678 eq2773531
  have eq2774094 : False := by grind
  exact eq2774094

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq65 X0 X2
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq124 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1 (M.op X0 X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq73
    | exact resolve eq73 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq696 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 (M.op X1 X0) X0 X2
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq124
    | exact resolve eq124 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq703 X0 X1 X2
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq703
    | exact resolve eq703 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq781 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X2 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 (M.op X2 (M.op X1 X0)) (M.op X0 X0) X2
       have i₂ := eq744 X0 X1 X2
       grind)
    | exact superpose eq744 eq124
    | exact resolve eq124 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq810 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq696
    | exact resolve eq696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq844 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq810 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq810
    | exact resolve eq810 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1023 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 X2
       have i₂ := eq844 X0 X2
       grind)
    | exact superpose eq844 eq71
    | exact resolve eq71 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1096 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 (M.op X0 X0) (M.op x (M.op X0 x)) X1
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1023
    | exact resolve eq1023 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X1) X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq1023 X1 X3 X0
       grind)
    | exact superpose eq1023 eq9
    | exact resolve eq9 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 (M.op X1 X0) (M.op X0 (M.op X2 X0)) X2
       have i₂ := eq1023 X0 X1 X2
       grind)
    | exact superpose eq1023 eq124
    | exact resolve eq124 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq1023 X1 X2 X0
       grind)
    | exact superpose eq1023 eq810
    | exact resolve eq810 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1147 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1145 X0 X1 X2
       have i₂ := eq844 X1 X2
       grind)
    | exact superpose eq844 eq1145
    | exact resolve eq1145 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1154 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1137 X0 X1 X2 X3
       have i₂ := eq844 X1 X0
       grind)
    | exact superpose eq844 eq1137
    | exact resolve eq1137 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1157 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1134 X0 X1 X2 X3
       have i₂ := eq844 X1 X3
       grind)
    | exact superpose eq844 eq1134
    | exact resolve eq1134 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq1134
  have eq1175 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X0 X1 X2
       have i₂ := eq1147 X0 X1 X0
       grind)
    | exact superpose eq1147 eq124
    | exact resolve eq124 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1250 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op X0 X0) X3)) = (M.op X0 (M.op (M.op X0 X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1175 (M.op X0 X0) X3 (M.op x (M.op X0 x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1175
    | exact resolve eq1175 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1175 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq1175 X0 X1 X2
       grind)
    | (have i₁ := eq1175 X1 (M.op X0 X1) X2
       have i₂ := eq1175 X0 X1 X2
       grind)
    | exact superpose eq1175 eq1175
    | exact resolve eq1175 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1352 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1268 X0 X1 X2 X3
       have i₂ := eq1023 X0 X1 X1
       grind)
    | exact superpose eq1023 eq1268
    | exact resolve eq1268 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023 eq1268
  have eq1390 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq1430 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X0 X3) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq1147 X2 (M.op X0 X3) X2
       grind)
    | exact superpose eq1147 eq62
    | exact resolve eq62 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1446 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1157 X0 X0 (M.op x (M.op X0 x)) X1
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1157
    | exact resolve eq1157 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1509 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X1))) (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1175 (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X3 X1)) X2
       have i₂ := eq1157 X0 X1 X2 X3
       grind)
    | exact superpose eq1157 eq1175
    | exact resolve eq1175 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1521 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X4 X1))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1509 X0 X1 X2 X3 X4
       have i₂ := eq125 (M.op X0 X1) X1
       grind)
    | exact superpose eq125 eq1509
    | exact resolve eq1509 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1544 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X1))) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1521 X0 X1 X2 X3 X4
       have i₂ := eq1147 X0 X1 X0
       grind)
    | exact superpose eq1147 eq1521
    | exact resolve eq1521 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq1521
  have eq1650 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1430 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1430
    | exact resolve eq1430 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2733 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1250 X0 (M.op (M.op X0 x) (M.op X2 (M.op X0 x)))
       have i₂ := eq1430 X0 X0 X2 x
       grind)
    | exact superpose eq1430 eq1250
    | exact resolve eq1250 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2738 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1250 X0 (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0)))
       have i₂ := eq1446 (M.op X0 X0) X1
       grind)
    | exact superpose eq1446 eq1250
    | exact resolve eq1250 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq2860 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2738 X0 X1
       have i₂ := eq1154 X0 (M.op X1 X1) X0 (M.op X1 X1)
       grind)
    | exact superpose eq1154 eq2738
    | exact resolve eq2738 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2862 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2733 X0 X1 X2
       have i₂ := eq1154 X0 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1154 eq2733
    | exact resolve eq2733 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq3354 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op X4 (M.op X5 (M.op X1 (M.op X2 (M.op X3 X0))))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1352 X0 (M.op X3 (M.op X1 (M.op X2 X0))) X2 X3
       have i₂ := eq781 X0 X1 X2 X3
       grind)
    | exact superpose eq781 eq1352
    | exact resolve eq1352 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3447 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1175 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq1352 X0 X1 X2 X3
       grind)
    | exact superpose eq1352 eq1175
    | exact resolve eq1175 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq3476 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3447 X0 X1 X2 X3 X4
       have i₂ := eq1154 X0 X1 X0 X1
       grind)
    | exact superpose eq1154 eq3447
    | exact resolve eq3447 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq3522 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op X4 (M.op X5 (M.op X1 (M.op X2 (M.op X3 X0))))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3354 X0 X1 X2 X3 X4 X5
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq3354
    | exact resolve eq3354 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq6099 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X1) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op X1 X1)))) (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1650 X1 X2 X4 (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1))) X3
       have i₂ := eq1096 X1 X0
       grind)
    | exact superpose eq1096 eq1650
    | exact resolve eq1650 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq6191 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq1390 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq1390 X0 X1
       grind)
    | exact superpose eq1390 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq1390 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq1390 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq1390 X0 X1
       grind)
    | exact resolve eq13 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6296 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq1390 X1 X0
       grind)
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq1390 X0 X0
       grind)
    | exact superpose eq1390 eq63
    | (have j1 := eq1390 X1 X0
       grind)
    | exact resolve eq63 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6309 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq6310 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309
  have eq6324 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6310 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6310
    | (have j0 := eq6310 X0 X1
       grind)
    | exact resolve eq6310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310
  have eq9061 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1096 X0 X1
       have i₂ := eq2860 X1 X0
       grind)
    | exact superpose eq2860 eq1096
    | exact resolve eq1096 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq2860
  have eq10055 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1430 X0 X1 X2 X3
       have i₂ := eq2862 X2 X0 X3
       grind)
    | exact superpose eq2862 eq1430
    | exact resolve eq1430 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq10090 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) = (M.op X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2862 X0 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq1446 X0 X1
       grind)
    | exact superpose eq1446 eq2862
    | exact resolve eq2862 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq2862
  have eq11098 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10055 (M.op X0 X0) X0 X1 X2
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq10055
    | exact resolve eq10055 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10055
  have eq12157 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X1 (M.op X2 (M.op X3 X0)))))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3476 (M.op X3 (M.op X1 (M.op X2 X0))) X0 X2 X3 X4
       have i₂ := eq781 X0 X1 X2 X3
       grind)
    | exact superpose eq781 eq3476
    | exact resolve eq3476 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq3476
  have eq12592 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X1 (M.op X2 (M.op X3 X0)))))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq12157 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12157
    | exact resolve eq12157 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12157
  have eq28846 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) = (M.op X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11098 X0 X1 (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))
       have i₂ := eq9061 (M.op X0 X0) X1
       grind)
    | exact superpose eq9061 eq11098
    | exact resolve eq11098 eq9061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9061 eq11098
  have eq29229 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) = (M.op X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28846 X0 X1 X2
       have i₂ := eq1175 X1 X1 X1
       grind)
    | exact superpose eq1175 eq28846
    | exact resolve eq28846 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28846
  have eq29324 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f29324_12 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) = (M.op X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))))) := by
      intro X0 X1 X2
      grind
    have f29324_13 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
      intro X0
      grind
    have f29324_22 : (M.op X2 (M.op X0 X1)) ≠ (M.op X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 X1)))) := by grind
    have f29324_24 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 X1)))) := by
      intro X0 X1 X2
      first
      | (have i₁ := f29324_12 X0 X0 X2
         have i₂ := f29324_13 X0
         grind)
      | exact superpose f29324_13 f29324_12
      | exact resolve f29324_12 f29324_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29324_82 : (M.op X2 (M.op X0 X1)) ≠ (M.op X2 (M.op X0 X1)) := by
      first
      | (have i₁ := f29324_22
         have i₂ := f29324_24 X0 X1 X2
         grind)
      | exact superpose f29324_24 f29324_22
      | (have r₁ := f29324_22
         have r₂ := f29324_24 X0 X1 X2
         grind)
      | exact resolve f29324_22 f29324_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29324_83 : False := by grind
    exact f29324_83
  clear eq29229
  have eq29683 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op X2 X2) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1175 X1 (M.op (M.op X1 X1) (M.op X2 (M.op X0 X1))) X2
       have i₂ := eq29324 X0 X1 X2
       grind)
    | exact superpose eq29324 eq1175
    | exact resolve eq1175 eq29324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq29324
  have eq29806 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29683 X0 X1 X2 X3
       have i₂ := eq1154 X0 (M.op X1 X2) X0 (M.op X2 X2)
       grind)
    | exact superpose eq1154 eq29683
    | exact resolve eq29683 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq29683
  have eq29968 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29806 X0 X1 X2 X3
       have i₂ := eq10090 X1 X2 X0
       grind)
    | exact superpose eq10090 eq29806
    | exact resolve eq29806 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10090 eq29806
  have eq45405 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6324 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324
  have eq55610 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op X2 (M.op X3 (M.op X4 (M.op (σ X0) (σ X1))))) (M.op (σ X0) (M.op (σ X0) (σ X1)))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6099 X0 (σ X0) (σ X1) X3 X4
       have i₂ := eq1390 X0 X1
       grind)
    | (have i₁ := eq6099 X0 (σ X1) (σ X1) X3 X4
       have i₂ := eq1390 X0 X1
       grind)
    | exact superpose eq1390 eq6099
    | (have j1 := eq1390 X1 X0
       grind)
    | exact resolve eq6099 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq6099
  have eq56030 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) (M.op (σ X0) (σ X1)))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55610 X0 X1 x x x
       have i₂ := eq1544 (σ X0) (M.op (σ X0) (σ X1)) x x x
       grind)
    | exact superpose eq1544 eq55610
    | (have j0 := eq55610 X0 X1 x x x
       grind)
    | exact resolve eq55610 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq55610
  have eq56201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (M.op (σ X0) (M.op (σ X0) (σ X1)))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56030 X0 X1
       have i₂ := eq29968 (σ X0) (σ X0) (σ X1) (σ X0)
       grind)
    | exact superpose eq29968 eq56030
    | (have j0 := eq56030 X0 X1
       grind)
    | exact resolve eq56030 eq29968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29968 eq56030
  have eq56261 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq6296 eq56201
    | (have j0 := eq56201 X0 X1
       have j1 := eq6296 X0 X1
       grind)
    | exact resolve eq56201 eq6296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6296 eq56201
  have eq56309 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq56261 X0 X1
       have j1 := eq45405 X1 X0
       grind)
    | (have r₁ := eq56261 X0 X1
       have r₂ := eq45405 X0 X1
       grind)
    | (have r₁ := eq56261 X1 X0
       have r₂ := eq45405 X0 X1
       grind)
    | exact resolve eq56261 eq45405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45405 eq56261
  have eq56364 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56309 X0 (M.op X0 X0)
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq56309
    | (have j0 := eq56309 X0 (M.op X0 X0)
       grind)
    | exact resolve eq56309 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq56376 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56309 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq56309
    | (have j0 := eq56309 (τ X1) (τ X0)
       grind)
    | exact resolve eq56309 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq56437 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56376 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56376
    | (have j0 := eq56376 X0 X1
       grind)
    | exact resolve eq56376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56376
  have eq56460 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56437 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq56437
    | (have j0 := eq56437 X0 X1
       grind)
    | exact resolve eq56437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56437
  have eq56465 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56460 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq56460
    | (have j0 := eq56460 X0 X1
       grind)
    | exact resolve eq56460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56460
  have eq56470 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56465 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56465
    | (have j0 := eq56465 X0 X1
       grind)
    | exact resolve eq56465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56465
  have eq56475 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56470 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56470
    | (have j0 := eq56470 X0 X1
       grind)
    | exact resolve eq56470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56470
  have eq160228 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq125 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq56364 X0
       grind)
    | exact superpose eq56364 eq125
    | (have j1 := eq56364 X0
       grind)
    | exact resolve eq125 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq160481 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq56364 eq160228
    | (have j0 := eq160228 X0
       have j1 := eq56364 X0
       grind)
    | exact resolve eq160228 eq56364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56364 eq160228
  have eq625887 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (σ X0)))))) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12592 (σ (M.op X0 X0)) X1 X2 (σ (M.op X0 X0)) X4 X5 x
       have i₂ := eq160481 X0
       grind)
    | exact superpose eq160481 eq12592
    | (have j1 := eq160481 X0
       grind)
    | exact resolve eq12592 eq160481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12592 eq160481
  have eq626228 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq625887 X0 x x x x x
       have i₂ := eq3522 (σ X0) x x x x x
       grind)
    | exact superpose eq3522 eq625887
    | (have j0 := eq625887 X0 x x x x x
       grind)
    | exact resolve eq625887 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522 eq625887
  have eq626229 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq626228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626228
  have eq626675 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56309 X0 X1
       have i₂ := eq626229 X0
       grind)
    | exact superpose eq626229 eq56309
    | (have j0 := eq56309 X0 X1
       grind)
    | exact resolve eq56309 eq626229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56309
  have eq626715 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq626229 X0
       grind)
    | exact superpose eq626229 eq63
    | exact resolve eq63 eq626229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626229
  have eq741421 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626675 X0 X1
       have i₂ := eq56475 X1 X0
       grind)
    | exact superpose eq56475 eq626675
    | (have j0 := eq626675 X0 X1
       have j1 := eq56475 X1 X0
       grind)
    | exact resolve eq626675 eq56475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56475 eq626675
  have eq857756 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq741421 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741421
  have eq857840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq857756 x y
       grind)
    | exact superpose eq857756 eq16
    | (have j1 := eq857756 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq857756 x y
       grind)
    | exact resolve eq16 eq857756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857756
  have eq858422 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq857840
  have eq858945 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq858422
       grind)
    | exact superpose eq858422 eq10
    | exact resolve eq10 eq858422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858422
  have eq859161 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq858945
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq858945
    | exact resolve eq858945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858945
  have eq859162 : y = (M.op x x) := by grind
  clear eq859161
  have eq859260 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq859162
       grind)
    | exact superpose eq859162 eq63
    | exact resolve eq63 eq859162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq859330 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq626715 x
       have i₂ := eq859162
       grind)
    | exact superpose eq859162 eq626715
    | exact resolve eq626715 eq859162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626715 eq859162
  have eq859865 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq859260
       grind)
    | exact superpose eq859260 eq16
    | exact resolve eq16 eq859260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859260
  have eq860358 : False := by grind
  exact eq860358

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq34 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq81 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq80 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq80
    | exact resolve eq80 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq85 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq81 (σ X0)
       grind)
    | exact superpose eq81 eq29
    | exact resolve eq29 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq162 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq162
    | (have j0 := eq162 (σ X0)
       grind)
    | exact resolve eq162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq333 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq532 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 (M.op X0 X1) X1
       have i₂ := eq55 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq52 X1 X1 X0 X2
       grind)
    | exact superpose eq52 eq63
    | exact resolve eq63 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq557 X2 X0 (M.op X0 X0) X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq557
    | exact resolve eq557 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq557 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq557
    | exact resolve eq557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq611 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq583 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq583
    | exact resolve eq583 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op X2 (M.op (σ X0) X3)) (M.op (σ X0) (σ X1))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X0) X2 X3
       have i₂ := eq333 X1 X0
       grind)
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq333 X0 X0
       grind)
    | exact superpose eq333 eq9
    | (have j1 := eq333 X1 X0
       grind)
    | exact resolve eq9 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = X2 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq333 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq333 X0 X0
       grind)
    | exact superpose eq333 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq333 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq333 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq333 X0 X0
       grind)
    | exact resolve eq13 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq333 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq333 X0 X1
       grind)
    | exact superpose eq333 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq333 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq333 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq333 X0 X0
       grind)
    | exact resolve eq13 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq333 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq717 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq716 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq719 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq717
    | (have j0 := eq717 X0 X1
       grind)
    | exact resolve eq717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq769 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0)
       have i₂ := eq611 X0 X1
       grind)
    | exact superpose eq611 eq53
    | exact resolve eq53 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq769 X0 X1
       grind)
    | exact superpose eq769 eq52
    | exact resolve eq52 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq808 X0 X1 X2
       have i₂ := eq611 X1 X0
       grind)
    | exact superpose eq611 eq808
    | exact resolve eq808 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq910 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq583 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq824 X0 X1 X2
       grind)
    | exact superpose eq824 eq583
    | exact resolve eq583 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq916 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq910 X0 X1 X2
       have i₂ := eq611 X1 X2
       grind)
    | exact superpose eq611 eq910
    | exact resolve eq910 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1292 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556 X0 X1 X2
       have i₂ := eq916 X0 X1 X0
       grind)
    | exact superpose eq916 eq556
    | exact resolve eq556 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq1302 : ∀ X0 X3 : G, (M.op X3 (M.op (M.op X0 X0) X3)) = (M.op X0 (M.op (M.op X0 X0) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1292 (M.op X0 X0) X3 (M.op x (M.op X0 x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1292
    | exact resolve eq1292 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1292 (M.op X1 X0) X0 X2
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq1292
    | exact resolve eq1292 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1292 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq1292 X0 X1 X2
       grind)
    | (have i₁ := eq1292 X1 (M.op X0 X1) X2
       have i₂ := eq1292 X0 X1 X2
       grind)
    | exact superpose eq1292 eq1292
    | exact resolve eq1292 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1427 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1329 X0 X1 X2 X3
       have i₂ := eq769 X0 X1
       grind)
    | exact superpose eq769 eq1329
    | exact resolve eq1329 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1434 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1321 X0 X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq1321
    | exact resolve eq1321 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1595 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq583 (M.op X1 (M.op X2 X0)) (M.op X0 X0)
       have i₂ := eq1434 X0 X1 X2
       grind)
    | exact superpose eq1434 eq583
    | exact resolve eq583 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq1614 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1595 X0 X1 X2
       have i₂ := eq611 (M.op X2 X0) X1
       grind)
    | exact superpose eq611 eq1595
    | exact resolve eq1595 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1910 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq88
    | (have j1 := eq163 X0
       grind)
    | exact resolve eq88 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq1956 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1910 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1910
    | (have j0 := eq1910 X0
       grind)
    | exact resolve eq1910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq2016 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1302 X0 (M.op X0 X1)
       have i₂ := eq1292 X0 X1 X0
       grind)
    | (have i₁ := eq1302 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq1292 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq1292 eq1302
    | exact resolve eq1302 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq2017 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1302 X1 (M.op x X1)
       have i₂ := eq916 X1 X1 x
       grind)
    | exact superpose eq916 eq1302
    | exact resolve eq1302 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq2020 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1302 X0 (M.op (M.op X2 (M.op X0 x)) (M.op X2 (M.op X0 x)))
       have i₂ := eq52 X0 X0 X2 x
       grind)
    | exact superpose eq52 eq1302
    | exact resolve eq1302 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2115 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2020 X0 X1 X2
       have i₂ := eq125 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq125 eq2020
    | exact resolve eq2020 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2118 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2017 X0 X1
       have i₂ := eq769 X0 X1
       grind)
    | exact superpose eq769 eq2017
    | exact resolve eq2017 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2119 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2016 X0 X1
       have i₂ := eq769 X0 X1
       grind)
    | exact superpose eq769 eq2016
    | exact resolve eq2016 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq2130 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2115 X0 X1 X2
       have i₂ := eq611 (M.op X1 X2) X0
       grind)
    | exact superpose eq611 eq2115
    | exact resolve eq2115 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq3454 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X2 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1427 X0 (M.op X1 (M.op X2 X0)) X2 X3
       have i₂ := eq573 X0 X1 X2
       grind)
    | exact superpose eq573 eq1427
    | exact resolve eq1427 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq1427
  have eq3639 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X2 X0)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3454 X0 X1 X2 X3 X4
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq3454
    | exact resolve eq3454 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454
  have eq3947 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq1956 X0
       grind)
    | exact superpose eq1956 eq88
    | (have j1 := eq1956 X0
       grind)
    | exact resolve eq88 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq3991 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq81 (σ X0)
       have i₂ := eq1956 X0
       grind)
    | exact superpose eq1956 eq81
    | (have j1 := eq1956 X0
       grind)
    | exact resolve eq81 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1956
  have eq3998 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3991 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3991
    | (have j0 := eq3991 X0
       grind)
    | exact resolve eq3991 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq4016 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3947 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3947
    | (have j0 := eq3947 X0
       grind)
    | exact resolve eq3947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947
  have eq4089 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ (σ X0)) = (σ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (σ X0) (σ X0)
       have i₂ := eq3998 (σ X0)
       grind)
    | exact superpose eq3998 eq34
    | (have j1 := eq3998 (σ X0)
       grind)
    | exact resolve eq34 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3998
  have eq4113 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (σ X0)) = (σ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4089 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4089
    | (have j0 := eq4089 X0
       grind)
    | exact resolve eq4089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4129 : ∀ X0 : G, (σ (σ X0)) = (σ (σ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4113 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4113
    | (have j0 := eq4113 X0
       grind)
    | exact resolve eq4113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4153 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq540 X0 X1 X2 X3 X4
       have i₂ := eq611 X0 X1
       grind)
    | exact superpose eq611 eq540
    | exact resolve eq540 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq4421 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4153 X0 X1 X3 (M.op X0 X0) X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq4153
    | exact resolve eq4153 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153
  have eq5055 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 (M.op X2 X1) X3 (M.op X1 (M.op X0 X1))
       have i₂ := eq4421 X1 X0 (M.op X2 X1) X2
       grind)
    | exact superpose eq4421 eq63
    | exact resolve eq63 eq4421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4421
  have eq5159 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5055 X0 X1 X2 X3
       have i₂ := eq611 X1 X2
       grind)
    | exact superpose eq611 eq5055
    | exact resolve eq5055 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq6246 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X0 X1 X2
       have i₂ := eq611 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq611 eq532
    | exact resolve eq532 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq6510 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6246 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq53 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq6246
    | exact resolve eq6246 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6246
  have eq8253 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq719 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq719
    | exact resolve eq719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq8361 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8253 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq8253
    | (have j0 := eq8253 X0 X1
       grind)
    | exact resolve eq8253 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8253
  have eq8367 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8361 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq8361
    | (have j0 := eq8361 X0 X1
       grind)
    | exact resolve eq8361 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8361
  have eq8797 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq542 X0 X1 X2 X3 X4 X5
       have i₂ := eq611 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq611 eq542
    | exact resolve eq542 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq611
  have eq8906 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X4 (M.op X5 (M.op X3 X0))) (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8797 X0 (M.op X1 X0) (M.op X0 X0) X3 X4 X5
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq8797
    | exact resolve eq8797 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8926 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op X4 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X3))))) = (M.op (M.op X8 (M.op X9 (M.op X6 (M.op X7 X2)))) (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X3)))) (M.op X4 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq8797 X0 (M.op X5 (M.op X4 X1)) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2)))) X3 X4 X5
       have i₂ := eq8797 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq8797 eq8797
    | exact resolve eq8797 eq8797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8797
  have eq10637 : ∀ X0 X1 : G, (k (τ X1) (σ (k X0 X0))) = (τ (k X1 (σ (σ X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ (k X0 X0))
       have i₂ := eq4129 X0
       grind)
    | exact superpose eq4129 eq23
    | (have j1 := eq4129 X0
       grind)
    | exact resolve eq23 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq10668 : ∀ X0 X1 : G, (k (τ X1) (σ (k X0 X0))) = (k (τ X1) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10637 X0 X1
       have i₂ := eq23 X1 (σ X0)
       grind)
    | exact superpose eq23 eq10637
    | (have j0 := eq10637 X0 X1
       grind)
    | exact resolve eq10637 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10637
  have eq10804 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (σ X3))) = X0 ∨ (σ (k X3 (τ X0))) = (M.op (σ X3) X0) ∨ (M.op X0 X0) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq696 (τ X0) X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq696
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq11006 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (σ X3))) = X0 ∨ (M.op (σ X3) X0) = (k (σ X3) X0) ∨ (M.op X0 X0) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10804 X0 X1 X2 X3
       have i₂ := eq19 X0 X3
       grind)
    | exact superpose eq19 eq10804
    | (have j0 := eq10804 X0 X1 X2 X3
       grind)
    | exact resolve eq10804 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10804
  have eq12055 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq697 X0 X1 (σ X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq12057 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq12055 X0 X1
       have j1 := eq715 X0 X1
       grind)
    | (have r₁ := eq12055 X0 X1
       have r₂ := eq715 X0 X1
       grind)
    | (have r₁ := eq12055 X1 X1
       have r₂ := eq715 X1 X1
       grind)
    | exact resolve eq12055 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq12055
  have eq12068 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12057 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12057
    | (have j0 := eq12057 X0 X1
       grind)
    | exact resolve eq12057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12057
  have eq15960 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2119 (M.op X0 X2) X1
       have i₂ := eq2130 X1 X0 X2
       grind)
    | exact superpose eq2130 eq2119
    | exact resolve eq2119 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq17363 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15960 X0 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq2118 X0 X1
       grind)
    | exact superpose eq2118 eq15960
    | exact resolve eq15960 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq15960
  have eq71914 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8367 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8367
    | exact resolve eq8367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8367
  have eq72267 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X4 (M.op X5 (M.op X3 X0))) (M.op X2 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8906 X0 X1 X2 X3 X4 X5
       have i₂ := eq2130 X1 X2 X0
       grind)
    | exact superpose eq2130 eq8906
    | exact resolve eq8906 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8906
  have eq73033 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 X2)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1302 (M.op x (M.op X3 X0)) (M.op X2 (M.op X1 (M.op X2 X0)))
       have i₂ := eq72267 X0 X1 X2 X3 (M.op x (M.op X3 X0)) x
       grind)
    | exact superpose eq72267 eq1302
    | exact resolve eq1302 eq72267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq72267
  have eq73503 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 X2)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq73033 X0 X1 X2 X3 X4
       have i₂ := eq5159 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq5159 eq73033
    | exact resolve eq73033 eq5159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5159 eq73033
  have eq73735 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 X2)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq73503 X0 X1 X2 X3 X4
       have i₂ := eq1614 X2 X0 X1
       grind)
    | exact superpose eq1614 eq73503
    | exact resolve eq73503 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq73503
  have eq95607 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X2 X0)) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11006 X0 X1 X2 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11006
    | exact resolve eq11006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11006
  have eq96992 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12068 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12068
    | exact resolve eq12068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12068
  have eq97324 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96992 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq96992
    | (have j0 := eq96992 X0 X1
       grind)
    | exact resolve eq96992 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96992
  have eq97334 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97324 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq97324
    | (have j0 := eq97324 X0 X1
       grind)
    | exact resolve eq97324 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq97324
  have eq224589 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq71914 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273161 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq224589 (M.op X1 X0) X0
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq224589
    | (have j0 := eq224589 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq224589 (M.op X1 X0) X0
       have r₂ := eq125 X0 X1
       grind)
    | exact resolve eq224589 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq224589
  have eq273350 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273161
  have eq338891 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op X4 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X3))))) = (M.op (M.op X8 (M.op X9 (M.op X6 (M.op X7 X2)))) (M.op X5 (M.op X4 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq8926 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
       have i₂ := eq2130 X4 X5 (M.op X0 (M.op X1 (M.op X2 X3)))
       grind)
    | exact superpose eq2130 eq8926
    | exact resolve eq8926 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8926
  have eq342420 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X6 X1)))) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))))) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq338891 (M.op X0 (M.op X1 X2)) X0 X1 X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2)) X5 X6 X3 X4
       have i₂ := eq6510 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq6510 eq338891
    | exact resolve eq338891 eq6510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6510 eq338891
  have eq343461 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X6 X1)))) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq342420 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq769 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq769 eq342420
    | exact resolve eq342420 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq342420
  have eq343924 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X6 X1)))) (M.op X0 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq343461 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq2130 (M.op X0 (M.op X1 X2)) X0 (M.op X1 X2)
       grind)
    | exact superpose eq2130 eq343461
    | exact resolve eq343461 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130 eq343461
  have eq344062 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X6 X1)))) (M.op X0 (M.op X2 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq343924 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq73735 X0 X1 X2 X0 X1
       grind)
    | exact superpose eq73735 eq343924
    | exact resolve eq343924 eq73735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73735 eq343924
  have eq344104 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X6 X1)))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq344062 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq17363 X1 X2 X0
       grind)
    | exact superpose eq17363 eq344062
    | exact resolve eq344062 eq17363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363 eq344062
  have eq1765419 : ∀ X0 X1 : G, (k X0 (σ X1)) = (k X0 (σ (k X1 X1))) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10668 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10668
    | (have j0 := eq10668 X1 X1
       grind)
    | exact resolve eq10668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10668
  have eq1767761 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k X0 (τ (σ (k X1 X1)))) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ (k X1 X1))
       have i₂ := eq1765419 (σ X0) X1
       grind)
    | exact superpose eq1765419 eq29
    | (have j1 := eq1765419 X0 X1
       grind)
    | exact resolve eq29 eq1765419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1765419
  have eq1768402 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k X0 (k X1 X1)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1767761 X0 X1
       have i₂ := eq10 (k X1 X1)
       grind)
    | exact superpose eq10 eq1767761
    | (have j0 := eq1767761 X0 X1
       grind)
    | exact resolve eq1767761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767761
  have eq1769497 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k X0 (k X1 X1)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1768402 X0 X1
       have i₂ := eq23 (σ X0) X1
       grind)
    | exact superpose eq23 eq1768402
    | (have j0 := eq1768402 X0 X1
       grind)
    | exact resolve eq1768402 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1768402
  have eq1770172 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X1 X1)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1769497 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1769497
    | (have j0 := eq1769497 X0 X1
       grind)
    | exact resolve eq1769497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769497
  have eq1772668 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1770172 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770172
  have eq1772676 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1772668 X0
       have j1 := eq4016 X0
       grind)
    | (have r₁ := eq1772668 X0
       have r₂ := eq4016 X0
       grind)
    | exact resolve eq1772668 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016 eq1772668
  have eq1773684 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq71914 X0 (k X0 X0)
       have i₂ := eq1772676 X0
       grind)
    | exact superpose eq1772676 eq71914
    | (have j0 := eq71914 X0 (k X0 X0)
       grind)
    | exact resolve eq71914 eq1772676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71914
  have eq1773967 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1773684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773684
  have eq1775552 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 (k X0 X0) (k X0 X0)
       have i₂ := eq1773967 X0
       grind)
    | exact superpose eq1773967 eq583
    | (have j1 := eq1773967 X0
       grind)
    | exact resolve eq583 eq1773967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq1773967
  have eq1775931 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1775552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775552
  have eq1776335 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1775931 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1775931
    | exact resolve eq1775931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1776821 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq273350 (k X0 X0) X0
       have i₂ := eq1775931 X0
       grind)
    | exact superpose eq1775931 eq273350
    | exact resolve eq273350 eq1775931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273350 eq1775931
  have eq1777194 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1776821 X0
       have i₂ := eq1772676 X0
       grind)
    | exact superpose eq1772676 eq1776821
    | (have j0 := eq1776821 X0
       grind)
    | exact resolve eq1776821 eq1772676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772676 eq1776821
  have eq1777195 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1777194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777194
  have eq1783538 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq55 (k X0 X0) (k X0 X0)
       have i₂ := eq1777195 X0
       grind)
    | exact superpose eq1777195 eq55
    | exact resolve eq55 eq1777195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777195
  have eq1785490 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1783538 (σ X0)
       grind)
    | exact superpose eq1783538 eq15
    | exact resolve eq15 eq1783538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785580 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq1783538 (τ X0)
       grind)
    | exact superpose eq1783538 eq32
    | exact resolve eq32 eq1783538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1785829 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1785580 X0
       have i₂ := eq1783538 X0
       grind)
    | exact superpose eq1783538 eq1785580
    | exact resolve eq1785580 eq1783538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785580
  have eq1785918 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1785490 X0
       have i₂ := eq1783538 X0
       grind)
    | exact superpose eq1783538 eq1785490
    | exact resolve eq1785490 eq1783538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785490
  have eq1795952 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1776335 X0
       have i₂ := eq1783538 X0
       grind)
    | exact superpose eq1783538 eq1776335
    | exact resolve eq1776335 eq1783538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776335 eq1783538
  have eq2688621 : ∀ X0 X1 X4 X5 X6 X7 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X7 X0)))) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X4 X5 X6 X7
    first
    | (have i₁ := eq344104 (M.op X1 (M.op x x)) x X0 x X4 X5 X6
       have i₂ := eq95607 X0 X1 x x
       grind)
    | exact superpose eq95607 eq344104
    | (have j1 := eq95607 X1 X1 X0 x
       grind)
    | exact resolve eq344104 eq95607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95607 eq344104
  have eq2694010 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2688621 X0 X1 x x x x
       have i₂ := eq3639 X0 x x x x
       grind)
    | exact superpose eq3639 eq2688621
    | (have j0 := eq2688621 X0 X1 x x x x
       grind)
    | exact resolve eq2688621 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639 eq2688621
  have eq2702130 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97334 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97334
    | exact resolve eq97334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97334
  have eq2871815 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2702130 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702130
  have eq2912645 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2871815 (σ X1) (σ X0)
       have i₂ := eq333 X1 X0
       grind)
    | (have i₁ := eq2871815 (σ X1) (σ X1)
       have i₂ := eq333 X0 X1
       grind)
    | exact superpose eq333 eq2871815
    | (have j0 := eq2871815 (σ X1) (σ X0)
       have j1 := eq333 X1 X0
       grind)
    | (have r₁ := eq2871815 (σ X0) (σ X0)
       have r₂ := eq333 X0 X0
       grind)
    | (have r₁ := eq2871815 (σ X1) (σ X1)
       have r₂ := eq333 X1 X1
       grind)
    | exact resolve eq2871815 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq2871815
  have eq2912878 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2912645 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912645
  have eq2913146 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2912878 X0 X1
       have j1 := eq2694010 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2912878 X0 X1
       have r₂ := eq2694010 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2912878 X0 X0
       have r₂ := eq2694010 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq2912878 X0 X1
       have r₂ := eq2694010 (σ X0) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq2912878 eq2694010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694010 eq2912878
  have eq2914150 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2913146 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2913146
    | (have j0 := eq2913146 X0 X1
       grind)
    | exact resolve eq2913146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913146
  have eq2914151 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2914150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914150
  have eq2914861 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2914151 X0 X1
       have i₂ := eq1785918 X0
       grind)
    | exact superpose eq1785918 eq2914151
    | (have j0 := eq2914151 X0 X1
       grind)
    | exact resolve eq2914151 eq1785918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785918 eq2914151
  have eq2916351 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2914861 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2914861
    | exact resolve eq2914861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2916934 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2914861 y x
       grind)
    | exact superpose eq2914861 eq16
    | (have j1 := eq2914861 y x
       grind)
    | exact resolve eq16 eq2914861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914861
  have eq2919261 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2916351 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2916351
    | (have j0 := eq2916351 X0 X1
       grind)
    | exact resolve eq2916351 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2916351
  have eq2928795 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2919261 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2919261
    | (have j0 := eq2919261 X1 (τ X0)
       grind)
    | exact resolve eq2919261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919261
  have eq2931511 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2928795 X0 X1
       have i₂ := eq1785829 X0
       grind)
    | exact superpose eq1785829 eq2928795
    | (have j0 := eq2928795 X0 X1
       grind)
    | exact resolve eq2928795 eq1785829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785829 eq2928795
  have eq2932226 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2931511 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2931511
    | (have j0 := eq2931511 X0 X1
       grind)
    | exact resolve eq2931511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931511
  have eq2939203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2916934
       have i₂ := eq2932226 y x
       grind)
    | exact superpose eq2932226 eq2916934
    | (have j1 := eq2932226 y x
       grind)
    | exact resolve eq2916934 eq2932226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916934 eq2932226
  have eq2939206 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2939203
  have eq2939260 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2939206
       grind)
    | exact superpose eq2939206 eq10
    | exact resolve eq10 eq2939206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939206
  have eq2940875 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2939260
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2939260
    | exact resolve eq2939260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939260
  have eq2940876 : x = (M.op y y) := by grind
  clear eq2940875
  have eq2941674 : x = (M.op x y) := by
    first
    | (have i₁ := eq62 y
       have i₂ := eq2940876
       grind)
    | exact superpose eq2940876 eq62
    | exact resolve eq62 eq2940876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2942035 : y = (M.op x x) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq2940876
       grind)
    | exact superpose eq2940876 eq55
    | exact resolve eq55 eq2940876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq2940876
  have eq2952676 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1795952 x
       have i₂ := eq2942035
       grind)
    | exact superpose eq2942035 eq1795952
    | exact resolve eq1795952 eq2942035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795952 eq2942035
  have eq3067688 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2952676
       grind)
    | exact superpose eq2952676 eq16
    | exact resolve eq16 eq2952676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952676
  have eq3068845 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3067688
       have i₂ := eq2941674
       grind)
    | exact superpose eq2941674 eq3067688
    | exact resolve eq3067688 eq2941674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941674 eq3067688
  have eq3068846 : False := by grind
  exact eq3068846
