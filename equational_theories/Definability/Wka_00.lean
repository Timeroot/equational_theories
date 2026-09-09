import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq23 (τ X0)
       grind)
    | exact superpose eq23 eq17
    | exact resolve eq17 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq27
    | exact resolve eq27 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq66 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq68 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq63
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq68
    | (have j0 := eq68 (σ X1) (σ X0)
       grind)
    | exact resolve eq68 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq68 (τ X1) X0
       grind)
    | exact superpose eq68 eq18
    | (have j1 := eq68 (τ X1) X0
       grind)
    | exact resolve eq18 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq68 X1 (τ X0)
       grind)
    | exact superpose eq68 eq17
    | (have j1 := eq68 X1 (τ X0)
       grind)
    | exact resolve eq17 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq246 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq231
    | (have j0 := eq231 X0 X1
       grind)
    | exact resolve eq231 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq257 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq246
    | (have j0 := eq246 X0 X1
       grind)
    | exact resolve eq246 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq255
    | (have j0 := eq255 X0 X1
       grind)
    | exact resolve eq255 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq345 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq564 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq606 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq564 X0 X1
       have j1 := eq102 X0 (σ X1)
       grind)
    | (have r₁ := eq564 X0 X0
       have r₂ := eq102 X0 (σ X0)
       grind)
    | (have r₁ := eq564 X0 X1
       have r₂ := eq102 X0 (σ X1)
       grind)
    | exact resolve eq564 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq564
  have eq658 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq606
    | (have j0 := eq606 X0 X1
       grind)
    | exact resolve eq606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq692 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq2807 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq216
    | exact resolve eq216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2968 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2807 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2807
    | (have j0 := eq2807 X0 X1
       grind)
    | exact resolve eq2807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2807
  have eq3518 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq257 X0 X1
       grind)
    | exact superpose eq257 eq345
    | (have j0 := eq345 X0 X1
       have j1 := eq257 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq257 X0 X1
       grind)
    | exact resolve eq345 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq345
  have eq3651 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3518 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq7046 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq712 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq712
    | (have j0 := eq712 (τ X0) (τ X1)
       grind)
    | exact resolve eq712 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq7116 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7046 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7046
    | (have j0 := eq7046 X0 X1
       grind)
    | exact resolve eq7046 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046
  have eq7142 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7116 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7116
    | (have j0 := eq7116 X0 X1
       grind)
    | exact resolve eq7116 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7116
  have eq7159 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7142 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7142
    | (have j0 := eq7142 X0 X1
       grind)
    | exact resolve eq7142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7142
  have eq7170 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7159 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7159
    | (have j0 := eq7159 X0 X1
       grind)
    | exact resolve eq7159 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7159
  have eq7175 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7170 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7170
    | (have j0 := eq7170 X0 X1
       grind)
    | exact resolve eq7170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq7178 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7175 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7175
    | (have j0 := eq7175 X0 X1
       grind)
    | exact resolve eq7175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq7179 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7178 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7178
    | (have j0 := eq7178 X0 X1
       grind)
    | exact resolve eq7178 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7178
  have eq8764 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq264 X0 X1
       grind)
    | exact superpose eq264 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq264 X0 X1
       grind)
    | exact resolve eq13 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq8891 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8764 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq8764
    | (have j0 := eq8764 X0 X1
       grind)
    | exact resolve eq8764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8764
  have eq9003 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8891 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq8891
    | (have j0 := eq8891 X0 X1
       grind)
    | exact resolve eq8891 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8891
  have eq9004 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9003 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9003
  have eq9078 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9004 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq9004
    | (have j0 := eq9004 X0 X1
       grind)
    | exact resolve eq9004 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9004
  have eq9102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9078 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9078
    | (have j0 := eq9078 X0 X1
       grind)
    | exact resolve eq9078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9078
  have eq9103 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9102
  have eq91739 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq3651 X1 (τ X0)
       grind)
    | exact superpose eq3651 eq18
    | (have j1 := eq3651 X1 (τ X0)
       grind)
    | exact resolve eq18 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq91778 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq3651 (σ X0) X1
       grind)
    | exact superpose eq3651 eq38
    | (have j1 := eq3651 (σ X0) X1
       grind)
    | exact resolve eq38 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651
  have eq91817 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91778 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq91778
    | (have j0 := eq91778 X0 X1
       grind)
    | exact resolve eq91778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91778
  have eq91826 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91739 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq91739
    | (have j0 := eq91739 X0 X1
       grind)
    | exact resolve eq91739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91739
  have eq91854 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91817 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq91817
    | (have j0 := eq91817 X0 X1
       grind)
    | exact resolve eq91817 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91817
  have eq91859 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91826 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq91826
    | (have j0 := eq91826 X0 X1
       grind)
    | exact resolve eq91826 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91826
  have eq91880 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91854 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq91854
    | (have j0 := eq91854 X0 X1
       grind)
    | exact resolve eq91854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91854
  have eq91885 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91859 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91859
    | (have j0 := eq91859 X0 X1
       grind)
    | exact resolve eq91859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91859
  have eq91896 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91880 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91880
    | (have j0 := eq91880 X0 X1
       grind)
    | exact resolve eq91880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91880
  have eq91899 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91885 X0 X1
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq91885
    | (have j0 := eq91885 X0 X1
       grind)
    | exact resolve eq91885 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq91885
  have eq91903 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91896 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91896
    | (have j0 := eq91896 X0 X1
       grind)
    | exact resolve eq91896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91896
  have eq93606 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq91903 (σ X0) X1
       grind)
    | exact superpose eq91903 eq38
    | (have j1 := eq91903 (σ X0) X1
       grind)
    | exact resolve eq38 eq91903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91903
  have eq93663 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93606 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq93606
    | (have j0 := eq93606 X0 X1
       grind)
    | exact resolve eq93606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93606
  have eq93814 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93663 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq93663
    | (have j0 := eq93663 X0 X1
       grind)
    | exact resolve eq93663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93663
  have eq104747 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7179 X1 X0
       have i₂ := eq91899 X0 X1
       grind)
    | exact superpose eq91899 eq7179
    | (have j0 := eq7179 X0 X1
       have j1 := eq91899 X1 X0
       grind)
    | (have r₁ := eq7179 X1 X0
       have r₂ := eq91899 X0 X1
       grind)
    | (have r₁ := eq7179 X1 X1
       have r₂ := eq91899 X1 X1
       grind)
    | exact resolve eq7179 eq91899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7179
  have eq104852 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91899 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91899
  have eq104868 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq104747 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104747
  have eq104971 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq104868 X0 X1
       have j1 := eq104852 X0 X1
       grind)
    | (have r₁ := eq104868 X0 X1
       have r₂ := eq104852 X0 X1
       grind)
    | (have r₁ := eq104868 X1 X0
       have r₂ := eq104852 X0 X1
       grind)
    | (have r₁ := eq104868 X1 X1
       have r₂ := eq104852 X1 X1
       grind)
    | exact resolve eq104868 eq104852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104852 eq104868
  have eq127364 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104971 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104971
    | (have j0 := eq104971 (σ X0) X1
       grind)
    | exact resolve eq104971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104971
  have eq127420 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq127364 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq127364
    | (have j0 := eq127364 X0 X1
       grind)
    | exact resolve eq127364 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq127364
  have eq165773 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq93814 X1 (σ X0)
       grind)
    | exact superpose eq93814 eq22
    | (have j1 := eq93814 X1 (σ X0)
       grind)
    | exact resolve eq22 eq93814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93814
  have eq165784 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165773 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq165773
    | (have j0 := eq165773 X0 X1
       grind)
    | exact resolve eq165773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165773
  have eq165820 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165784 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq165784
    | (have j0 := eq165784 X0 X1
       grind)
    | exact resolve eq165784 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165784
  have eq165850 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165820 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq165820
    | (have j0 := eq165820 X0 X1
       grind)
    | exact resolve eq165820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165820
  have eq165871 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165850 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165850
    | (have j0 := eq165850 X0 X1
       grind)
    | exact resolve eq165850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165850
  have eq165883 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq165871 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq165871
    | (have j0 := eq165871 X0 X1
       grind)
    | exact resolve eq165871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165871
  have eq180440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq165883 y x
       grind)
    | exact superpose eq165883 eq16
    | (have j1 := eq165883 y x
       grind)
    | exact resolve eq16 eq165883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165883
  have eq185270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq180440
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq180440
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq180440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq180440
       have i₂ := eq2968 y x
       grind)
    | exact superpose eq2968 eq180440
    | (have j1 := eq2968 y x
       grind)
    | (have r₁ := eq180440
       have r₂ := eq2968 y x
       grind)
    | exact resolve eq180440 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968 eq180440
  have eq185282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq185274
  have eq185283 : (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq185282
  have eq185288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq185270
  have eq185289 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq185288
  have eq185291 : (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq185283
       have r₂ := eq12 x y
       grind)
    | exact resolve eq185283 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185283
  have eq186454 : (M.op y y) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by grind
  clear eq185291
  have eq259166 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq127420 X1 (σ X0)
       grind)
    | exact superpose eq127420 eq22
    | (have j1 := eq127420 X1 (σ X0)
       grind)
    | exact resolve eq22 eq127420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq127420
  have eq259171 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259166 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq259166
    | (have j0 := eq259166 X0 X1
       grind)
    | exact resolve eq259166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259166
  have eq259183 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259171 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq259171
    | (have j0 := eq259171 X0 X1
       grind)
    | exact resolve eq259171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259171
  have eq259190 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259183 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq259183
    | (have j0 := eq259183 X0 X1
       grind)
    | exact resolve eq259183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259183
  have eq259194 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259190 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq259190
    | (have j0 := eq259190 X0 X1
       grind)
    | exact resolve eq259190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259190
  have eq259195 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq259194 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq259194
    | (have j0 := eq259194 X0 X1
       grind)
    | exact resolve eq259194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq259194
  have eq266325 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k x y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq259195 y x
       grind)
    | exact superpose eq259195 eq16
    | (have j1 := eq259195 y x
       grind)
    | exact resolve eq16 eq259195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259195
  have eq273583 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq266325
       have i₂ := eq185289
       grind)
    | exact superpose eq185289 eq266325
    | exact resolve eq266325 eq185289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266325
  have eq273584 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq273583
  have eq273585 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq273584
  have eq421153 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9103 (τ X0) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9103
    | (have j0 := eq9103 (τ X0) X1
       grind)
    | exact resolve eq9103 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq421159 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq421153 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq421153
    | (have j0 := eq421153 X0 X1
       grind)
    | exact resolve eq421153 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421153
  have eq421163 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq421159 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq421159
    | (have j0 := eq421159 X0 X1
       grind)
    | exact resolve eq421159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421159
  have eq421167 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq421163 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq421163
    | (have j0 := eq421163 X0 X1
       grind)
    | exact resolve eq421163 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421163
  have eq426206 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq421167 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq421167
    | exact resolve eq421167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421167
  have eq426214 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq426206 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq426206
    | (have j0 := eq426206 X0 X1
       grind)
    | exact resolve eq426206 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq426206
  have eq426225 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq426214 y x
       have i₂ := eq273585
       grind)
    | exact superpose eq273585 eq426214
    | (have j0 := eq426214 y x
       grind)
    | exact resolve eq426214 eq273585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273585 eq426214
  have eq426228 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq426225
  have eq426230 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq426228
       have r₂ := eq185289
       grind)
    | exact resolve eq426228 eq185289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185289 eq426228
  have eq426237 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq426230
       grind)
    | exact superpose eq426230 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq426230
       grind)
    | exact resolve eq12 eq426230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426249 : (M.op y y) = (k x y) := by grind
  clear eq426237
  have eq426277 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9103 x y
       have i₂ := eq426249
       grind)
    | exact superpose eq426249 eq9103
    | (have j0 := eq9103 x y
       grind)
    | exact resolve eq9103 eq426249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9103 eq426249
  have eq426313 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq426277
  have eq426669 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq426313
       grind)
    | exact superpose eq426313 eq16
    | exact resolve eq16 eq426313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426681 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq426669
       have i₂ := eq426230
       grind)
    | exact superpose eq426230 eq426669
    | exact resolve eq426669 eq426230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426669
  have eq426682 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq426681
  have eq426732 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq426682
       grind)
    | exact superpose eq426682 eq10
    | exact resolve eq10 eq426682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426682
  have eq426871 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq426732
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq426732
    | exact resolve eq426732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426732
  have eq426876 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq186454
       have i₂ := eq426871
       grind)
    | exact superpose eq426871 eq186454
    | (have r₁ := eq186454
       have r₂ := eq426871
       grind)
    | exact resolve eq186454 eq426871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186454 eq426871
  have eq427037 : (M.op x x) = (k x y) := by grind
  clear eq426876
  have eq427083 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq573 x y
       have i₂ := eq427037
       grind)
    | exact superpose eq427037 eq573
    | (have j0 := eq573 x y
       grind)
    | exact resolve eq573 eq427037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq427037
  have eq427132 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq427083
  have eq427145 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq427132
       have r₂ := eq426313
       grind)
    | exact resolve eq427132 eq426313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426313 eq427132
  have eq427160 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq427145
       grind)
    | exact superpose eq427145 eq16
    | exact resolve eq16 eq427145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427145
  have eq427199 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq427160
       have i₂ := eq426230
       grind)
    | exact superpose eq426230 eq427160
    | exact resolve eq427160 eq426230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426230 eq427160
  have eq427200 : False := by grind
  exact eq427200

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq23 (τ X0)
       grind)
    | exact superpose eq23 eq17
    | exact resolve eq17 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq25
    | exact resolve eq25 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq27
    | exact resolve eq27 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq58 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq63 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq14 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq14 (τ X0) (τ X0)
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq68
    | (have j0 := eq68 (σ X1) (σ X0)
       grind)
    | exact resolve eq68 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq68 X1 (τ X0)
       grind)
    | exact superpose eq68 eq17
    | (have j1 := eq68 X1 (τ X0)
       grind)
    | exact resolve eq17 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq236 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq68 (τ X0) X1
       grind)
    | exact superpose eq68 eq18
    | (have j1 := eq68 (τ X0) X1
       grind)
    | exact resolve eq18 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq249 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq260 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq249
    | (have j0 := eq249 X0 X1
       grind)
    | exact resolve eq249 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq255
    | (have j0 := eq255 X0 X1
       grind)
    | exact resolve eq255 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq345 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq564 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X1 X0
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq606 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq564 X0 X1
       have j1 := eq102 X0 (σ X1)
       grind)
    | (have r₁ := eq564 X0 X0
       have r₂ := eq102 X0 (σ X0)
       grind)
    | (have r₁ := eq564 X0 X1
       have r₂ := eq102 X0 (σ X1)
       grind)
    | exact resolve eq564 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq564
  have eq658 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq606
    | (have j0 := eq606 X0 X1
       grind)
    | exact resolve eq606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq692 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq3083 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq236 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq236
    | exact resolve eq236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq3252 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3083 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3083
    | (have j0 := eq3083 X0 X1
       grind)
    | exact resolve eq3083 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3506 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq260 X1 X0
       grind)
    | exact superpose eq260 eq11
    | (have j1 := eq260 X1 X0
       grind)
    | exact resolve eq11 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3520 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq260 X0 X1
       grind)
    | exact superpose eq260 eq345
    | (have j0 := eq345 X0 X1
       have j1 := eq260 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq260 X0 X1
       grind)
    | exact resolve eq345 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq345
  have eq3638 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520
  have eq4111 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq30 X1
       have i₂ := eq58 (τ X1) X1
       grind)
    | exact superpose eq58 eq30
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq30 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq7021 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X1 X0
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq712
    | (have j0 := eq712 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | exact resolve eq712 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq7030 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq712 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq712
    | (have j0 := eq712 (τ X0) (τ X1)
       grind)
    | exact resolve eq712 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq712
  have eq7076 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7021 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7021
  have eq7100 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7030 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7030
    | (have j0 := eq7030 X0 X1
       grind)
    | exact resolve eq7030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7030
  have eq7126 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7100 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7100
    | (have j0 := eq7100 X0 X1
       grind)
    | exact resolve eq7100 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100
  have eq7143 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7126 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7126
    | (have j0 := eq7126 X0 X1
       grind)
    | exact resolve eq7126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126
  have eq7154 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7143 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7143
    | (have j0 := eq7143 X0 X1
       grind)
    | exact resolve eq7143 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7143
  have eq7159 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7154 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7154
    | (have j0 := eq7154 X0 X1
       grind)
    | exact resolve eq7154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7154
  have eq7162 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7159 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7159
    | (have j0 := eq7159 X0 X1
       grind)
    | exact resolve eq7159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7159
  have eq7163 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7162 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7162
    | (have j0 := eq7162 X0 X1
       grind)
    | exact resolve eq7162 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7162
  have eq8744 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq264 X0 X1
       grind)
    | exact superpose eq264 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq264 X0 X1
       grind)
    | exact resolve eq13 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq8871 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8744 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq8744
    | (have j0 := eq8744 X0 X1
       grind)
    | exact resolve eq8744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8744
  have eq8983 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8871 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq8871
    | (have j0 := eq8871 X0 X1
       grind)
    | exact resolve eq8871 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8871
  have eq8984 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq8983 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8983
  have eq9058 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8984 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq8984
    | (have j0 := eq8984 X0 X1
       grind)
    | exact resolve eq8984 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8984
  have eq9082 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9058 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9058
    | (have j0 := eq9058 X0 X1
       grind)
    | exact resolve eq9058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9058
  have eq9083 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9082 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9082
  have eq89983 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq3638 (σ X0) X1
       grind)
    | exact superpose eq3638 eq38
    | (have j1 := eq3638 (σ X0) X1
       grind)
    | exact resolve eq38 eq3638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq90022 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq89983 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq89983
    | (have j0 := eq89983 X0 X1
       grind)
    | exact resolve eq89983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89983
  have eq90059 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90022 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq90022
    | (have j0 := eq90022 X0 X1
       grind)
    | exact resolve eq90022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90022
  have eq90085 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90059 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq90059
    | (have j0 := eq90059 X0 X1
       grind)
    | exact resolve eq90059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90059
  have eq90101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90085 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90085
    | (have j0 := eq90085 X0 X1
       grind)
    | exact resolve eq90085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90085
  have eq90108 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90101 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90101
    | (have j0 := eq90101 X0 X1
       grind)
    | exact resolve eq90101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90101
  have eq91808 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq90108 (σ X0) X1
       grind)
    | exact superpose eq90108 eq38
    | (have j1 := eq90108 (σ X0) X1
       grind)
    | exact resolve eq38 eq90108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq90108
  have eq91865 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91808 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq91808
    | (have j0 := eq91808 X0 X1
       grind)
    | exact resolve eq91808 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91808
  have eq92016 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91865 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq91865
    | (have j0 := eq91865 X0 X1
       grind)
    | exact resolve eq91865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91865
  have eq163921 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq92016 X1 (σ X0)
       grind)
    | exact superpose eq92016 eq22
    | (have j1 := eq92016 X1 (σ X0)
       grind)
    | exact resolve eq22 eq92016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq92016
  have eq163932 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163921 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq163921
    | (have j0 := eq163921 X0 X1
       grind)
    | exact resolve eq163921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163921
  have eq163968 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163932 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq163932
    | (have j0 := eq163932 X0 X1
       grind)
    | exact resolve eq163932 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163932
  have eq163998 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163968 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq163968
    | (have j0 := eq163968 X0 X1
       grind)
    | exact resolve eq163968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163968
  have eq164019 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163998 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163998
    | (have j0 := eq163998 X0 X1
       grind)
    | exact resolve eq163998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163998
  have eq164031 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq164019 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq164019
    | (have j0 := eq164019 X0 X1
       grind)
    | exact resolve eq164019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164019
  have eq178598 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164031 x y
       grind)
    | exact superpose eq164031 eq16
    | (have j1 := eq164031 x y
       grind)
    | exact resolve eq16 eq164031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164031
  have eq183435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq178598
       have i₂ := eq3252 x y
       grind)
    | exact superpose eq3252 eq178598
    | (have j1 := eq3252 x y
       grind)
    | (have r₁ := eq178598
       have r₂ := eq3252 x y
       grind)
    | exact resolve eq178598 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252 eq178598
  have eq183442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq183435
  have eq183443 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq183442
  have eq183451 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq183443
       have r₂ := eq12 y x
       grind)
    | exact resolve eq183443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183443
  have eq184602 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq7163 y x
       have i₂ := eq183451
       grind)
    | exact superpose eq183451 eq7163
    | (have j0 := eq7163 y x
       grind)
    | (have r₁ := eq7163 y x
       have r₂ := eq183451
       grind)
    | exact resolve eq7163 eq183451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7163
  have eq184616 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
  have eq184620 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq184602
  have eq184630 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq184620
       have r₂ := eq184616
       grind)
    | exact resolve eq184620 eq184616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184616 eq184620
  have eq415622 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq415639 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq415622 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq415622
    | (have j0 := eq415622 X0 X1
       grind)
    | exact resolve eq415622 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415622
  have eq416367 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3506 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3506
    | (have j0 := eq3506 X1 (σ X0)
       grind)
    | exact resolve eq3506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq416382 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416367 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq416367
    | (have j0 := eq416367 X0 X1
       grind)
    | exact resolve eq416367 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416367
  have eq416385 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416382 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq416382
    | (have j0 := eq416382 X0 X1
       grind)
    | exact resolve eq416382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416382
  have eq416388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416385 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq416385
    | (have j0 := eq416385 X0 X1
       grind)
    | exact resolve eq416385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416385
  have eq416421 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq416388 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416388
  have eq416843 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq416421 y x
       have i₂ := eq184630
       grind)
    | exact superpose eq184630 eq416421
    | (have j0 := eq416421 y x
       grind)
    | exact resolve eq416421 eq184630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416421
  have eq416847 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq416843
  have eq418280 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4111 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4111
    | exact resolve eq4111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq418307 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq418280 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq418280
    | (have j0 := eq418280 X0 X1
       grind)
    | exact resolve eq418280 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq418280
  have eq418313 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq418307 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq418307
    | (have j0 := eq418307 X0 X1
       grind)
    | exact resolve eq418307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418307
  have eq418346 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq418313 y x
       have i₂ := eq184630
       grind)
    | exact superpose eq184630 eq418313
    | (have j0 := eq418313 y x
       grind)
    | exact resolve eq418313 eq184630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184630 eq418313
  have eq418382 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq418346
  have eq418409 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq418382
       have r₂ := eq416847
       grind)
    | exact resolve eq418382 eq416847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416847 eq418382
  have eq423597 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7076 y x
       grind)
    | exact superpose eq7076 eq16
    | (have j1 := eq7076 y x
       grind)
    | exact resolve eq16 eq7076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7076
  have eq423600 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq415639 x y
       grind)
    | (have r₁ := eq423597
       have r₂ := eq415639 x y
       grind)
    | exact resolve eq423597 eq415639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415639 eq423597
  have eq423605 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq423600
       grind)
    | exact superpose eq423600 eq10
    | exact resolve eq10 eq423600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423600
  have eq423617 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq423605
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq423605
    | exact resolve eq423605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423605
  have eq423619 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq61 x y
       grind)
    | (have r₁ := eq423617
       have r₂ := eq61 x y
       grind)
    | (have r₁ := eq423617
       have r₂ := eq61 y x
       grind)
    | exact resolve eq423617 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq423617
  have eq423621 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq423619
       have i₂ := eq183451
       grind)
    | exact superpose eq183451 eq423619
    | exact resolve eq423619 eq183451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183451 eq423619
  have eq423783 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by grind
  clear eq423621
  have eq423785 : (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq423783
       have r₂ := eq12 y x
       grind)
    | exact resolve eq423783 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423783
  have eq423808 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq575 x y
       have i₂ := eq423785
       grind)
    | exact superpose eq423785 eq575
    | (have j0 := eq575 x y
       grind)
    | exact resolve eq575 eq423785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq423816 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9083 y x
       have i₂ := eq423785
       grind)
    | exact superpose eq423785 eq9083
    | (have j0 := eq9083 y x
       grind)
    | exact resolve eq9083 eq423785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9083
  have eq423847 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq423816
  have eq423849 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq423808
  have eq424298 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq423847
       grind)
    | exact superpose eq423847 eq16
    | exact resolve eq16 eq423847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423847
  have eq424311 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq424298
       have i₂ := eq418409
       grind)
    | exact superpose eq418409 eq424298
    | (have r₁ := eq424298
       have r₂ := eq418409
       grind)
    | exact resolve eq424298 eq418409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418409 eq424298
  have eq424316 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq424311
  have eq424326 : (M.op x y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq424316
       grind)
    | exact superpose eq424316 eq10
    | exact resolve eq10 eq424316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424316
  have eq424372 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq424326
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq424326
    | exact resolve eq424326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424326
  have eq424373 : (M.op x y) = (M.op x x) := by grind
  clear eq424372
  have eq424378 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq424373
       grind)
    | exact superpose eq424373 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq424373
       grind)
    | exact resolve eq13 eq424373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424393 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
  clear eq424378
  have eq424396 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq424393
       have i₂ := eq423785
       grind)
    | exact superpose eq423785 eq424393
    | exact resolve eq424393 eq423785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423785 eq424393
  have eq424397 : (M.op x x) = (M.op y y) := by grind
  clear eq424396
  have eq424690 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq423849
       have i₂ := eq424397
       grind)
    | exact superpose eq424397 eq423849
    | exact resolve eq423849 eq424397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423849 eq424397
  have eq424695 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq424690
  have eq424703 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq424695
       grind)
    | exact superpose eq424695 eq16
    | exact resolve eq16 eq424695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424695
  have eq424745 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq424703
       have i₂ := eq424373
       grind)
    | exact superpose eq424373 eq424703
    | exact resolve eq424703 eq424373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424373 eq424703
  have eq424746 : False := by grind
  exact eq424746

/-- `Equation2847`: `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation2847 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2847 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2847.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq32 (τ X0)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq37
    | exact resolve eq37 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq85 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq79 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq79 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq79 X1 X1
       have r₂ := eq77 X1 X1
       grind)
    | exact resolve eq79 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq79
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq119 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq10
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1
       have i₂ := eq80 X0 (τ X1)
       grind)
    | exact superpose eq80 eq41
    | (have j1 := eq80 X0 (τ X1)
       grind)
    | exact resolve eq41 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq188 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 X0 X1
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq199 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq145 X1
       grind)
    | exact superpose eq145 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ X1) (σ X0)
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq85 (τ X0) X1
       grind)
    | exact superpose eq85 eq18
    | (have j1 := eq85 (τ X0) X1
       grind)
    | exact resolve eq18 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq85 X1 (τ X0)
       grind)
    | exact superpose eq85 eq17
    | (have j1 := eq85 X1 (τ X0)
       grind)
    | exact resolve eq17 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq85
  have eq291 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq306 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq291
    | (have j0 := eq291 X0 X1
       grind)
    | exact resolve eq291 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq315 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq302
    | (have j0 := eq302 X0 X1
       grind)
    | exact resolve eq302 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq332 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq973 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X1 X0
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X1 X0
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1029 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq973 X0 X1
       have j1 := eq119 X0 (σ X1)
       grind)
    | (have r₁ := eq973 X0 X0
       have r₂ := eq119 X0 (σ X0)
       grind)
    | (have r₁ := eq973 X0 X1
       have r₂ := eq119 X0 (σ X1)
       grind)
    | exact resolve eq973 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq973
  have eq1081 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq1029
    | (have j0 := eq1029 X0 X1
       grind)
    | exact resolve eq1029 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1115 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1135 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1115
    | (have j0 := eq1115 X0 X1
       grind)
    | exact resolve eq1115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq4204 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq258 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq258
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq4397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4204 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4204
    | (have j0 := eq4204 X0 X1
       grind)
    | exact resolve eq4204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq5191 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq332
    | (have j0 := eq332 X0 X1
       have j1 := eq306 X0 X1
       grind)
    | (have r₁ := eq332 X0 X1
       have r₂ := eq306 X0 X1
       grind)
    | exact resolve eq332 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq332
  have eq5339 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5191
  have eq9174 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1135 (τ X1) (τ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq1135
    | (have j0 := eq1135 (τ X0) (τ X1)
       grind)
    | exact resolve eq1135 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq9256 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9174 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9174
    | (have j0 := eq9174 X0 X1
       grind)
    | exact resolve eq9174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9174
  have eq9287 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9256 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq9256
    | (have j0 := eq9256 X0 X1
       grind)
    | exact resolve eq9256 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9256
  have eq9309 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9287 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9287
    | (have j0 := eq9287 X0 X1
       grind)
    | exact resolve eq9287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9287
  have eq9325 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9309 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq9309
    | (have j0 := eq9309 X0 X1
       grind)
    | exact resolve eq9309 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9309
  have eq9334 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9325 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9325
    | (have j0 := eq9325 X0 X1
       grind)
    | exact resolve eq9325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq9339 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9334 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9334
    | (have j0 := eq9334 X0 X1
       grind)
    | exact resolve eq9334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq9340 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9339 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq9339
    | (have j0 := eq9339 X0 X1
       grind)
    | exact resolve eq9339 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9339
  have eq11127 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq315 X0 X1
       grind)
    | exact superpose eq315 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq315 X0 X1
       grind)
    | exact resolve eq13 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq11269 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11127 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq11127
    | (have j0 := eq11127 X0 X1
       grind)
    | exact resolve eq11127 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11127
  have eq11390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11269 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq11269
    | (have j0 := eq11269 X0 X1
       grind)
    | exact resolve eq11269 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11269
  have eq11391 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11390
  have eq11473 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11391 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq11391
    | (have j0 := eq11391 X0 X1
       grind)
    | exact resolve eq11391 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11391
  have eq11499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11473 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11473
    | (have j0 := eq11473 X0 X1
       grind)
    | exact resolve eq11473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11473
  have eq11500 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11499 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11499
  have eq79805 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq5339 X1 (τ X0)
       grind)
    | exact superpose eq5339 eq18
    | (have j1 := eq5339 X1 (τ X0)
       grind)
    | exact resolve eq18 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq79849 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq5339 (σ X0) X1
       grind)
    | exact superpose eq5339 eq28
    | (have j1 := eq5339 (σ X0) X1
       grind)
    | exact resolve eq28 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339
  have eq79888 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq79849 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq79849
    | (have j0 := eq79849 X0 X1
       grind)
    | exact resolve eq79849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79849
  have eq79899 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79805 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq79805
    | (have j0 := eq79805 X0 X1
       grind)
    | exact resolve eq79805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79805
  have eq79929 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq79888 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq79888
    | (have j0 := eq79888 X0 X1
       grind)
    | exact resolve eq79888 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79888
  have eq79934 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79899 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq79899
    | (have j0 := eq79899 X0 X1
       grind)
    | exact resolve eq79899 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq79899
  have eq79955 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq79929 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq79929
    | (have j0 := eq79929 X0 X1
       grind)
    | exact resolve eq79929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79929
  have eq79960 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79934 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79934
    | (have j0 := eq79934 X0 X1
       grind)
    | exact resolve eq79934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79934
  have eq79971 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq79955 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79955
    | (have j0 := eq79955 X0 X1
       grind)
    | exact resolve eq79955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79955
  have eq79974 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq79960 X0 X1
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq79960
    | (have j0 := eq79960 X0 X1
       grind)
    | exact resolve eq79960 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq79960
  have eq79978 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79971 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79971
    | (have j0 := eq79971 X0 X1
       grind)
    | exact resolve eq79971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79971
  have eq81363 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq79978 (σ X0) X1
       grind)
    | exact superpose eq79978 eq28
    | (have j1 := eq79978 (σ X0) X1
       grind)
    | exact resolve eq28 eq79978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79978
  have eq81424 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81363 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq81363
    | (have j0 := eq81363 X0 X1
       grind)
    | exact resolve eq81363 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81363
  have eq81570 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81424 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq81424
    | (have j0 := eq81424 X0 X1
       grind)
    | exact resolve eq81424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81424
  have eq90456 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9340 X1 X0
       have i₂ := eq79974 X0 X1
       grind)
    | exact superpose eq79974 eq9340
    | (have j0 := eq9340 X0 X1
       have j1 := eq79974 X1 X0
       grind)
    | (have r₁ := eq9340 X1 X0
       have r₂ := eq79974 X0 X1
       grind)
    | (have r₁ := eq9340 X1 X1
       have r₂ := eq79974 X1 X1
       grind)
    | exact resolve eq9340 eq79974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90566 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq79974 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79974
  have eq90582 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90456
  have eq90690 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90582 X0 X1
       have j1 := eq90566 X0 X1
       grind)
    | (have r₁ := eq90582 X0 X1
       have r₂ := eq90566 X0 X1
       grind)
    | (have r₁ := eq90582 X1 X0
       have r₂ := eq90566 X0 X1
       grind)
    | (have r₁ := eq90582 X1 X1
       have r₂ := eq90566 X1 X1
       grind)
    | exact resolve eq90582 eq90566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90566 eq90582
  have eq108067 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90690 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90690
    | (have j0 := eq90690 (σ X0) X1
       grind)
    | exact resolve eq90690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90690
  have eq108125 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108067 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq108067
    | (have j0 := eq108067 X0 X1
       grind)
    | exact resolve eq108067 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq108067
  have eq138695 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq81570 X1 (σ X0)
       grind)
    | exact superpose eq81570 eq22
    | (have j1 := eq81570 X1 (σ X0)
       grind)
    | exact resolve eq22 eq81570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81570
  have eq138706 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138695 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq138695
    | (have j0 := eq138695 X0 X1
       grind)
    | exact resolve eq138695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138695
  have eq138744 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138706 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq138706
    | (have j0 := eq138706 X0 X1
       grind)
    | exact resolve eq138706 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138706
  have eq138774 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138744 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq138744
    | (have j0 := eq138744 X0 X1
       grind)
    | exact resolve eq138744 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138744
  have eq138795 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138774 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138774
    | (have j0 := eq138774 X0 X1
       grind)
    | exact resolve eq138774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138774
  have eq138807 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138795 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq138795
    | (have j0 := eq138795 X0 X1
       grind)
    | exact resolve eq138795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138795
  have eq151822 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138807 x y
       grind)
    | exact superpose eq138807 eq16
    | (have j1 := eq138807 x y
       grind)
    | exact resolve eq16 eq138807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138807
  have eq152294 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq151822
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq151822
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq151822 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152298 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq151822
       have i₂ := eq4397 x y
       grind)
    | exact superpose eq4397 eq151822
    | (have j1 := eq4397 x y
       grind)
    | (have r₁ := eq151822
       have r₂ := eq4397 x y
       grind)
    | exact resolve eq151822 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397 eq151822
  have eq152306 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq152298
  have eq152307 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq152306
  have eq152312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq152294
  have eq152313 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq152312
  have eq152315 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq152307
       have r₂ := eq12 y x
       grind)
    | exact resolve eq152307 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152307
  have eq153105 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq9340 y x
       have i₂ := eq152315
       grind)
    | exact superpose eq152315 eq9340
    | (have j0 := eq9340 y x
       grind)
    | (have r₁ := eq9340 y x
       have r₂ := eq152315
       grind)
    | exact resolve eq9340 eq152315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq153120 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
  have eq153124 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq153105
  have eq153135 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq153124
       have r₂ := eq153120
       grind)
    | exact resolve eq153124 eq153120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153124
  have eq204199 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq108125 X1 (σ X0)
       grind)
    | exact superpose eq108125 eq22
    | (have j1 := eq108125 X1 (σ X0)
       grind)
    | exact resolve eq22 eq108125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108125
  have eq204204 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204199 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq204199
    | (have j0 := eq204199 X0 X1
       grind)
    | exact resolve eq204199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204199
  have eq204217 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204204 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq204204
    | (have j0 := eq204204 X0 X1
       grind)
    | exact resolve eq204204 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204204
  have eq204224 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204217 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq204217
    | (have j0 := eq204217 X0 X1
       grind)
    | exact resolve eq204217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204217
  have eq204228 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204224 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq204224
    | (have j0 := eq204224 X0 X1
       grind)
    | exact resolve eq204224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204224
  have eq204229 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq204228 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq204228
    | (have j0 := eq204228 X0 X1
       grind)
    | exact resolve eq204228 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204228
  have eq204817 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq204229 x y
       grind)
    | exact superpose eq204229 eq16
    | (have j1 := eq204229 x y
       grind)
    | exact resolve eq16 eq204229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204229
  have eq306162 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq199 X1 X0
       grind)
    | exact superpose eq199 eq11
    | (have j1 := eq199 X1 X0
       grind)
    | exact resolve eq11 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq447251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306162 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq306162
    | (have j0 := eq306162 (σ X0) X1
       grind)
    | exact resolve eq306162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306162
  have eq447267 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq447251 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq447251
    | (have j0 := eq447251 X0 X1
       grind)
    | exact resolve eq447251 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447251
  have eq447270 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq447267 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq447267
    | (have j0 := eq447267 X0 X1
       grind)
    | exact resolve eq447267 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq447267
  have eq447273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq447270 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq447270
    | (have j0 := eq447270 X0 X1
       grind)
    | exact resolve eq447270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447270
  have eq447881 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq447273 x y
       have i₂ := eq152315
       grind)
    | exact superpose eq152315 eq447273
    | (have j0 := eq447273 x y
       grind)
    | exact resolve eq447273 eq152315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152315 eq447273
  have eq447918 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq447881
       have r₂ := eq12 y x
       grind)
    | exact resolve eq447881 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447881
  have eq467235 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq447918
       grind)
    | exact superpose eq447918 eq10
    | exact resolve eq10 eq447918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447918
  have eq467245 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq467235
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq467235
    | exact resolve eq467235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467235
  have eq467246 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
    first
    | (have r₁ := eq467245
       have r₂ := eq153120
       grind)
    | exact resolve eq467245 eq153120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153120 eq467245
  have eq467868 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq204817
       have i₂ := eq467246
       grind)
    | exact superpose eq467246 eq204817
    | (have r₁ := eq204817
       have r₂ := eq467246
       grind)
    | exact resolve eq204817 eq467246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204817 eq467246
  have eq467892 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
  clear eq467868
  have eq467893 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
  clear eq467892
  have eq477788 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq467893
  have eq477796 : (M.op x x) = (k y x) := by
    first
    | (have r₁ := eq477788
       have r₂ := eq153135
       grind)
    | exact resolve eq477788 eq153135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153135 eq477788
  have eq487818 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq988 x y
       have i₂ := eq477796
       grind)
    | exact superpose eq477796 eq988
    | (have j0 := eq988 x y
       grind)
    | exact resolve eq988 eq477796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq487819 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq989 x y
       have i₂ := eq477796
       grind)
    | exact superpose eq477796 eq989
    | (have j0 := eq989 x y
       grind)
    | exact resolve eq989 eq477796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq487845 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq487819
  have eq487846 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq487818
  have eq531237 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq487845
       grind)
    | exact superpose eq487845 eq16
    | exact resolve eq16 eq487845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487845
  have eq534607 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq531237
       have i₂ := eq152313
       grind)
    | exact superpose eq152313 eq531237
    | exact resolve eq531237 eq152313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531237
  have eq534612 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq534607
  have eq537980 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq534612
       grind)
    | exact superpose eq534612 eq16
    | exact resolve eq16 eq534612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904930 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11500 y x
       have i₂ := eq477796
       grind)
    | exact superpose eq477796 eq11500
    | (have j0 := eq11500 y x
       grind)
    | exact resolve eq11500 eq477796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11500
  have eq904932 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq904930
  have eq904937 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq534612
       have i₂ := eq904932
       grind)
    | exact superpose eq904932 eq534612
    | exact resolve eq534612 eq904932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534612 eq904932
  have eq904941 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq904937
  have eq904954 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq904941
       have i₂ := eq152313
       grind)
    | exact superpose eq152313 eq904941
    | exact resolve eq904941 eq152313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152313 eq904941
  have eq904989 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq904954
  have eq905008 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq904989
       have r₂ := eq537980
       grind)
    | exact resolve eq904989 eq537980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537980 eq904989
  have eq905026 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq905008
       grind)
    | exact superpose eq905008 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq905008
       grind)
    | exact resolve eq13 eq905008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905047 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
  clear eq905026
  have eq905050 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq905047
       have i₂ := eq477796
       grind)
    | exact superpose eq477796 eq905047
    | exact resolve eq905047 eq477796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477796 eq905047
  have eq905051 : (M.op x x) = (M.op y y) := by grind
  clear eq905050
  have eq905073 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq487846
       have i₂ := eq905051
       grind)
    | exact superpose eq905051 eq487846
    | exact resolve eq487846 eq905051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487846 eq905051
  have eq905240 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq905073
  have eq905283 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq905240
       grind)
    | exact superpose eq905240 eq16
    | exact resolve eq16 eq905240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905240
  have eq905314 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq905283
       have i₂ := eq905008
       grind)
    | exact superpose eq905008 eq905283
    | exact resolve eq905283 eq905008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905008 eq905283
  have eq905315 : False := by grind
  exact eq905315

/-- `Equation307`: `x ◇ x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pxy_pyx_Equation307 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law307 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law307.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq37 (σ X0) (σ X1)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq37 X0 (τ X1)
       grind)
    | exact superpose eq37 eq19
    | (have j1 := eq37 X0 (τ X1)
       grind)
    | exact resolve eq19 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq37
  have eq197 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq198 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq250 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq198 (σ X0)
       grind)
    | exact superpose eq198 eq15
    | exact resolve eq15 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq250 X0
       have i₂ := eq198 X0
       grind)
    | exact superpose eq198 eq250
    | exact resolve eq250 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq250
  have eq408 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq257 X0
       grind)
    | exact superpose eq257 eq9
    | exact resolve eq9 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1866 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1972 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1866 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1866
    | (have j0 := eq1866 X0 X1
       grind)
    | exact resolve eq1866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq3003 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq10
    | (have j1 := eq72 X0 X1
       grind)
    | exact resolve eq10 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3125 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X0 X1
       have i₂ := eq257 X0
       grind)
    | exact superpose eq257 eq3003
    | (have j0 := eq3003 X0 X1
       grind)
    | exact resolve eq3003 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq3003
  have eq3226 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3125 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3125
    | (have j0 := eq3125 X0 X1
       grind)
    | exact resolve eq3125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125
  have eq3836 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3226 x y
       grind)
    | exact superpose eq3226 eq16
    | (have j1 := eq3226 x y
       grind)
    | exact resolve eq16 eq3226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226
  have eq3900 : y = (M.op x x) := by
    first
    | (have j1 := eq1972 y x
       grind)
    | (have r₁ := eq3836
       have r₂ := eq1972 y x
       grind)
    | exact resolve eq3836 eq1972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972 eq3836
  have eq4136 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 x
       have i₂ := eq3900
       grind)
    | exact superpose eq3900 eq9
    | exact resolve eq9 eq3900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4147 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq408 x
       have i₂ := eq3900
       grind)
    | exact superpose eq3900 eq408
    | exact resolve eq408 eq3900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq3900
  have eq4851 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4147
       grind)
    | exact superpose eq4147 eq16
    | exact resolve eq16 eq4147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147
  have eq4855 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4851
       have i₂ := eq4136
       grind)
    | exact superpose eq4136 eq4851
    | exact resolve eq4851 eq4136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136 eq4851
  have eq4856 : False := by grind
  exact eq4856

/-- `Equation307`: `x ◇ x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyy_pxy_Equation307 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law307 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law307.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq352 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq31
  have eq643 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4339 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq352 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq4341 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339
  have eq4342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4492 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4342 (σ X0)
       grind)
    | exact superpose eq4342 eq15
    | exact resolve eq15 eq4342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4511 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4492 X0
       have i₂ := eq4342 X0
       grind)
    | exact superpose eq4342 eq4492
    | exact resolve eq4492 eq4342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4342 eq4492
  have eq5268 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq4511 X0
       grind)
    | exact superpose eq4511 eq9
    | exact resolve eq9 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5271 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5331 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5271 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq5271
    | exact resolve eq5271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5345 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5331
  have eq7876 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq8325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7876 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7876
    | (have j0 := eq7876 X0 X1
       grind)
    | exact resolve eq7876 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7876
  have eq30961 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq643 X1 X0
       grind)
    | exact superpose eq643 eq10
    | (have j1 := eq643 X1 X0
       grind)
    | exact resolve eq10 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq31359 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30961 X0 X1
       have i₂ := eq4511 X0
       grind)
    | exact superpose eq4511 eq30961
    | (have j0 := eq30961 X0 X1
       grind)
    | exact resolve eq30961 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30961
  have eq31904 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31359 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq31359
    | (have j0 := eq31359 X0 X1
       grind)
    | exact resolve eq31359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31359
  have eq32374 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31904 X0 X1
       have i₂ := eq4511 X1
       grind)
    | exact superpose eq4511 eq31904
    | (have j0 := eq31904 X0 X1
       grind)
    | exact resolve eq31904 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4511 eq31904
  have eq32701 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32374 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq32374
    | (have j0 := eq32374 X0 X1
       grind)
    | exact resolve eq32374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32374
  have eq93624 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32701 y x
       grind)
    | exact superpose eq32701 eq16
    | (have j1 := eq32701 y x
       grind)
    | exact resolve eq16 eq32701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32701
  have eq94030 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq8325 x y
       grind)
    | (have r₁ := eq93624
       have r₂ := eq8325 x y
       grind)
    | exact resolve eq93624 eq8325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8325 eq93624
  have eq95663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5345 y
       have i₂ := eq94030
       grind)
    | exact superpose eq94030 eq5345
    | exact resolve eq5345 eq94030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345 eq94030
  have eq95718 : y = (M.op x x) := by
    first
    | (have r₁ := eq95663
       have r₂ := eq16
       grind)
    | exact resolve eq95663 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95663
  have eq99713 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 x
       have i₂ := eq95718
       grind)
    | exact superpose eq95718 eq9
    | exact resolve eq9 eq95718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99731 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5268 x
       have i₂ := eq95718
       grind)
    | exact superpose eq95718 eq5268
    | exact resolve eq5268 eq95718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268 eq95718
  have eq105480 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99731
       grind)
    | exact superpose eq99731 eq16
    | exact resolve eq16 eq99731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99731
  have eq105499 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq105480
       have i₂ := eq99713
       grind)
    | exact superpose eq99713 eq105480
    | exact resolve eq105480 eq99713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99713 eq105480
  have eq105500 : False := by grind
  exact eq105500

/-- `Equation307`: `x ◇ x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation307 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law307 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law307.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq73 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq56 X0 (τ X1)
       grind)
    | exact superpose eq56 eq20
    | (have j1 := eq56 X0 (τ X1)
       grind)
    | exact resolve eq20 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq56 (σ X0) (σ X1)
       grind)
    | exact superpose eq56 eq15
    | (have j1 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq56
  have eq214 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq260 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq215 (σ X0)
       grind)
    | exact superpose eq215 eq15
    | exact resolve eq15 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq260 X0
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq260
    | exact resolve eq260 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq260
  have eq655 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq267 X0
       grind)
    | exact superpose eq267 eq9
    | exact resolve eq9 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1802 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1904 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1802 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1802
    | (have j0 := eq1802 X0 X1
       grind)
    | exact resolve eq1802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq3296 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq10
    | (have j1 := eq75 X0 X1
       grind)
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3419 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3296 X0 X1
       have i₂ := eq267 X0
       grind)
    | exact superpose eq267 eq3296
    | (have j0 := eq3296 X0 X1
       grind)
    | exact resolve eq3296 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq3296
  have eq3524 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3419 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3419
    | (have j0 := eq3419 X0 X1
       grind)
    | exact resolve eq3419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq4075 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3524 x y
       grind)
    | exact superpose eq3524 eq16
    | (have j1 := eq3524 x y
       grind)
    | exact resolve eq16 eq3524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq4144 : y = (M.op x x) := by
    first
    | (have j1 := eq1904 y x
       grind)
    | (have r₁ := eq4075
       have r₂ := eq1904 y x
       grind)
    | exact resolve eq4075 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904 eq4075
  have eq4389 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 x
       have i₂ := eq4144
       grind)
    | exact superpose eq4144 eq9
    | exact resolve eq9 eq4144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4406 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq655 x
       have i₂ := eq4144
       grind)
    | exact superpose eq4144 eq655
    | exact resolve eq655 eq4144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq4144
  have eq5597 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4406
       grind)
    | exact superpose eq4406 eq16
    | exact resolve eq16 eq4406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4406
  have eq5608 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5597
       have i₂ := eq4389
       grind)
    | exact superpose eq4389 eq5597
    | exact resolve eq5597 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389 eq5597
  have eq5609 : False := by grind
  exact eq5609

/-- `Equation3254`: `x ◇ x = x ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pxy_pyx_Equation3254 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3254 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3254.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq52 (σ X0) (σ X1)
       grind)
    | exact superpose eq52 eq15
    | (have j1 := eq52 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq52 X0 (τ X1)
       grind)
    | exact superpose eq52 eq19
    | (have j1 := eq52 X0 (τ X1)
       grind)
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq52
  have eq274 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq275 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq274 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq311 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
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
  have eq318 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq311
    | exact resolve eq311 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq311
  have eq682 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq26
    | exact resolve eq26 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2049 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1938 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1938
    | (have j0 := eq1938 X0 X1
       grind)
    | exact resolve eq1938 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq3741 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq10
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq10 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq3878 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3741 X0 X1
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq3741
    | (have j0 := eq3741 X0 X1
       grind)
    | exact resolve eq3741 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq3741
  have eq3989 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3878 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3878
    | (have j0 := eq3878 X0 X1
       grind)
    | exact resolve eq3878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq4225 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3989 x y
       grind)
    | exact superpose eq3989 eq16
    | (have j1 := eq3989 x y
       grind)
    | exact resolve eq16 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq4299 : y = (M.op x x) := by
    first
    | (have j1 := eq2049 y x
       grind)
    | (have r₁ := eq4225
       have r₂ := eq2049 y x
       grind)
    | exact resolve eq4225 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq4225
  have eq4455 : y = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq4299
       grind)
    | exact superpose eq4299 eq26
    | exact resolve eq26 eq4299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4466 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq682 x
       have i₂ := eq4299
       grind)
    | exact superpose eq4299 eq682
    | exact resolve eq682 eq4299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq4299
  have eq5368 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4466
       grind)
    | exact superpose eq4466 eq16
    | exact resolve eq16 eq4466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq5376 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5368
       have i₂ := eq4455
       grind)
    | exact superpose eq4455 eq5368
    | exact resolve eq5368 eq4455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455 eq5368
  have eq5377 : False := by grind
  exact eq5377

/-- `Equation3254`: `x ◇ x = x ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyy_pxy_Equation3254 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3254 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3254.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq247 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq44
  have eq705 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq10
    | (have j1 := eq49 X0 X1
       grind)
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq7275 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq247 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq7277 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275
  have eq7278 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7277
  have eq7461 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7278 (σ X0)
       grind)
    | exact superpose eq7278 eq15
    | exact resolve eq15 eq7278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7480 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7461 X0
       have i₂ := eq7278 X0
       grind)
    | exact superpose eq7278 eq7461
    | exact resolve eq7461 eq7278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7278 eq7461
  have eq8458 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq8460 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq7480 X0
       grind)
    | exact superpose eq7480 eq26
    | exact resolve eq26 eq7480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8559 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8458 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq8458
    | exact resolve eq8458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq8575 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq8559
  have eq11102 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq11638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11102 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11102
    | (have j0 := eq11102 X0 X1
       grind)
    | exact resolve eq11102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11102
  have eq33423 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq705 X1 X0
       grind)
    | exact superpose eq705 eq10
    | (have j1 := eq705 X1 X0
       grind)
    | exact resolve eq10 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq33824 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33423 X0 X1
       have i₂ := eq7480 X0
       grind)
    | exact superpose eq7480 eq33423
    | (have j0 := eq33423 X0 X1
       grind)
    | exact resolve eq33423 eq7480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33423
  have eq34355 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33824 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq33824
    | (have j0 := eq33824 X0 X1
       grind)
    | exact resolve eq33824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33824
  have eq34802 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34355 X0 X1
       have i₂ := eq7480 X1
       grind)
    | exact superpose eq7480 eq34355
    | (have j0 := eq34355 X0 X1
       grind)
    | exact resolve eq34355 eq7480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7480 eq34355
  have eq35110 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34802 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq34802
    | (have j0 := eq34802 X0 X1
       grind)
    | exact resolve eq34802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34802
  have eq129885 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35110 y x
       grind)
    | exact superpose eq35110 eq16
    | (have j1 := eq35110 y x
       grind)
    | exact resolve eq16 eq35110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35110
  have eq130441 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq11638 x y
       grind)
    | (have r₁ := eq129885
       have r₂ := eq11638 x y
       grind)
    | exact resolve eq129885 eq11638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11638 eq129885
  have eq131418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8575 y
       have i₂ := eq130441
       grind)
    | exact superpose eq130441 eq8575
    | exact resolve eq8575 eq130441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8575 eq130441
  have eq131502 : y = (M.op x x) := by
    first
    | (have r₁ := eq131418
       have r₂ := eq16
       grind)
    | exact resolve eq131418 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131418
  have eq131692 : y = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq131502
       grind)
    | exact superpose eq131502 eq26
    | exact resolve eq26 eq131502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq131718 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8460 x
       have i₂ := eq131502
       grind)
    | exact superpose eq131502 eq8460
    | exact resolve eq8460 eq131502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460 eq131502
  have eq137438 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131718
       grind)
    | exact superpose eq131718 eq16
    | exact resolve eq16 eq131718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131718
  have eq137478 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq137438
       have i₂ := eq131692
       grind)
    | exact superpose eq131692 eq137438
    | exact resolve eq137438 eq131692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131692 eq137438
  have eq137479 : False := by grind
  exact eq137479
