import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq29 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op X2 X2) X0) X2) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (M.op X2 X2) X2 X1
       have i₂ := eq60 X2
       grind)
    | exact superpose eq60 eq29
    | exact resolve eq29 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq68 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq82 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq68
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq94 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq94 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq95
    | exact resolve eq95 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq96
    | exact resolve eq96 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq96
  have eq119 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq9
    | exact resolve eq9 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq1127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       have j1 := eq172 X1 X0
       grind)
    | (have r₁ := eq174 X1 X0
       have r₂ := eq172 X0 X1
       grind)
    | (have r₁ := eq174 X0 (M.op X1 X1)
       have r₂ := eq172 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq174 X1 X1
       have r₂ := eq172 (k X1 X1) X1
       grind)
    | exact resolve eq174 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq174
  have eq1286 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1292 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1286 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1286 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1286 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq1286 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1286 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1301 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1292 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1292
    | (have j0 := eq1292 (σ X0) (σ X1)
       grind)
    | exact resolve eq1292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1292 (τ X0) X1
       grind)
    | exact superpose eq1292 eq17
    | (have j1 := eq1292 (τ X0) X1
       grind)
    | exact resolve eq17 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1292
  have eq1337 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (M.op X1 X0) X2 X1
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2854 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1321 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1321
    | exact resolve eq1321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq2963 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2854 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2854
    | (have j0 := eq2854 X0 X1
       grind)
    | exact resolve eq2854 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq8177 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1301 y x
       grind)
    | exact superpose eq1301 eq16
    | (have j1 := eq1301 y x
       grind)
    | exact resolve eq16 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq8375 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8177
       have i₂ := eq2963 y x
       grind)
    | exact superpose eq2963 eq8177
    | (have j1 := eq2963 (σ y) (σ x)
       grind)
    | (have r₁ := eq8177
       have r₂ := eq2963 y x
       grind)
    | exact resolve eq8177 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963 eq8177
  have eq8376 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8375
  have eq8411 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82 (σ y) (σ x)
       have i₂ := eq8376
       grind)
    | exact superpose eq8376 eq82
    | exact resolve eq82 eq8376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8376
  have eq8450 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8411
       have i₂ := eq99 x
       grind)
    | exact superpose eq99 eq8411
    | exact resolve eq8411 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq8411
  have eq8488 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq8450
       grind)
    | exact superpose eq8450 eq10
    | exact resolve eq10 eq8450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8450
  have eq8551 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8488
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8488
    | exact resolve eq8488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8488
  have eq8588 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq82 y x
       have i₂ := eq8551
       grind)
    | exact superpose eq8551 eq82
    | exact resolve eq82 eq8551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8551
  have eq8618 : x = (M.op x x) := by grind
  clear eq8588
  have eq8643 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 x X0
       have i₂ := eq8618
       grind)
    | exact superpose eq8618 eq68
    | exact resolve eq68 eq8618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq8647 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 x X0
       have i₂ := eq8618
       grind)
    | exact superpose eq8618 eq119
    | exact resolve eq119 eq8618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq8744 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1337 x x x
       have i₂ := eq8618
       grind)
    | exact superpose eq8618 eq1337
    | exact resolve eq1337 eq8618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8618
  have eq8753 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq8744 X0
       have i₂ := eq82 X0 x
       grind)
    | exact superpose eq82 eq8744
    | exact resolve eq8744 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq8744
  have eq8871 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8643 X0
       have i₂ := eq8753 X0
       grind)
    | exact superpose eq8753 eq8643
    | exact resolve eq8643 eq8753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8643 eq8753
  have eq8915 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1337 X1 x X0
       have i₂ := eq8871 X0
       grind)
    | exact superpose eq8871 eq1337
    | exact resolve eq1337 eq8871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq8948 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8915 X0 X0
       have i₂ := eq8871 X0
       grind)
    | exact superpose eq8871 eq8915
    | exact resolve eq8915 eq8871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq9538 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8647 X0
       have i₂ := eq8948 X0 (σ x)
       grind)
    | exact superpose eq8948 eq8647
    | exact resolve eq8647 eq8948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8647 eq8948
  have eq9545 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9538 (σ y)
       grind)
    | exact superpose eq9538 eq16
    | exact resolve eq16 eq9538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9538
  have eq9597 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq9545
       have i₂ := eq8871 y
       grind)
    | exact superpose eq8871 eq9545
    | exact resolve eq9545 eq8871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8871 eq9545
  have eq9598 : False := by grind
  exact eq9598

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq43 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq46
    | exact resolve eq46 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq46
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq53 X1
       grind)
    | exact superpose eq53 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq78 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq78 X0 (M.op X1 X1)
       have r₂ := eq76 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq78 X1 X1
       have r₂ := eq76 (k X1 X1) X1
       grind)
    | exact resolve eq78 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq78
  have eq113 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq123 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq9
    | exact resolve eq9 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq113 (σ X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq113
    | exact resolve eq113 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq83
    | (have j0 := eq83 (σ X0) (σ X1)
       grind)
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq233 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq229 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq229 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq229 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq229 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq363 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq9
    | exact resolve eq9 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq657 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq776 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq783 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq776 X0 X1
       have j1 := eq241 X1 X0
       grind)
    | (have r₁ := eq776 X1 X0
       have r₂ := eq241 X0 X1
       grind)
    | exact resolve eq776 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq776
  have eq836 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq657 X0 X1
       grind)
    | exact superpose eq657 eq9
    | exact resolve eq9 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq233 (τ X1) X0
       grind)
    | exact superpose eq233 eq17
    | (have j1 := eq233 (τ X1) X0
       grind)
    | exact resolve eq17 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq233
  have eq1976 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq783 x y
       grind)
    | exact superpose eq783 eq16
    | (have j1 := eq783 x y
       grind)
    | exact resolve eq16 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq19439 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1169 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1169
    | exact resolve eq1169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq19679 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19439 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq19439
    | (have j0 := eq19439 X0 X1
       grind)
    | exact resolve eq19439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19439
  have eq26821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1976
       have i₂ := eq19679 y x
       grind)
    | exact superpose eq19679 eq1976
    | (have j1 := eq19679 (σ y) (σ x)
       grind)
    | (have r₁ := eq1976
       have r₂ := eq19679 y x
       grind)
    | exact resolve eq1976 eq19679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976 eq19679
  have eq26822 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26821
  have eq27187 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq657 (σ x) (σ y)
       have i₂ := eq26822
       grind)
    | exact superpose eq26822 eq657
    | exact resolve eq657 eq26822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26822
  have eq27195 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27187
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq27187
    | exact resolve eq27187 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq27187
  have eq28259 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq27195
       grind)
    | exact superpose eq27195 eq10
    | exact resolve eq10 eq27195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27195
  have eq28348 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28259
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28259
    | exact resolve eq28259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28259
  have eq29201 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq657 x y
       have i₂ := eq28348
       grind)
    | exact superpose eq28348 eq657
    | exact resolve eq657 eq28348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28348
  have eq29207 : x = (M.op x x) := by grind
  clear eq29201
  have eq30043 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq363 x X0
       have i₂ := eq29207
       grind)
    | exact superpose eq29207 eq363
    | exact resolve eq363 eq29207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq30076 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq29207
       grind)
    | exact superpose eq29207 eq9
    | exact resolve eq9 eq29207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30149 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq836 x x x
       have i₂ := eq29207
       grind)
    | exact superpose eq29207 eq836
    | exact resolve eq836 eq29207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29207
  have eq30159 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq30149 X0
       have i₂ := eq657 x X0
       grind)
    | exact superpose eq657 eq30149
    | exact resolve eq30149 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq30149
  have eq31627 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30076 X0
       have i₂ := eq30159 X0
       grind)
    | exact superpose eq30159 eq30076
    | exact resolve eq30076 eq30159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31773 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq836 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq30076 X0
       grind)
    | exact superpose eq30076 eq836
    | exact resolve eq836 eq30076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq30076
  have eq31795 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31773 X0 X1
       have i₂ := eq30159 X0
       grind)
    | exact superpose eq30159 eq31773
    | exact resolve eq31773 eq30159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30159 eq31773
  have eq31847 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31795 X0 X0
       have i₂ := eq31627 X0
       grind)
    | exact superpose eq31627 eq31795
    | exact resolve eq31795 eq31627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31795
  have eq44455 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30043 X0
       have i₂ := eq31847 X0 (σ x)
       grind)
    | exact superpose eq31847 eq30043
    | exact resolve eq30043 eq31847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30043 eq31847
  have eq45132 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44455 (σ y)
       grind)
    | exact superpose eq44455 eq16
    | exact resolve eq16 eq44455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44455
  have eq45459 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq45132
       have i₂ := eq31627 y
       grind)
    | exact superpose eq31627 eq45132
    | exact resolve eq45132 eq31627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31627 eq45132
  have eq45460 : False := by grind
  exact eq45460

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_x_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq64 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq23 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op X2 X2) X0) X2) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 (M.op X2 X2) X2 X1
       have i₂ := eq64 X2
       grind)
    | exact superpose eq64 eq23
    | exact resolve eq23 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq125 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq125 X1 X0
       grind)
    | exact superpose eq125 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X1 X0) X2 X1
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1375 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       have j1 := eq103 X1 X0
       grind)
    | (have r₁ := eq105 X1 X0
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq105 X0 (M.op X1 X1)
       have r₂ := eq103 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq105 X1 X1
       have r₂ := eq103 (k X1 X1) X1
       grind)
    | exact resolve eq105 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq105
  have eq1634 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1641 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1634 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1634 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1634 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq1634 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1634 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq1660 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1641 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1641
    | (have j0 := eq1641 (σ X0) (σ X1)
       grind)
    | exact resolve eq1641 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1684 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1641 (τ X0) X1
       grind)
    | exact superpose eq1641 eq17
    | (have j1 := eq1641 (τ X0) X1
       grind)
    | exact resolve eq17 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1641
  have eq1877 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1684 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1684
    | exact resolve eq1684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1954 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq3535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1660 y x
       grind)
    | exact superpose eq1660 eq16
    | (have j1 := eq1660 y x
       grind)
    | exact resolve eq16 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3602 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1660 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq3877 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X1 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3602 (τ X0) (τ X1)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq3602
    | (have j0 := eq3602 (τ X0) (τ X1)
       grind)
    | exact resolve eq3602 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3602
  have eq3887 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3877 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq3877
    | (have j0 := eq3877 X0 X1
       grind)
    | exact resolve eq3877 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877
  have eq3892 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3887 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3887
    | (have j0 := eq3887 X0 X1
       grind)
    | exact resolve eq3887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3896 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3892 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3892
    | (have j0 := eq3892 X0 X1
       grind)
    | exact resolve eq3892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892
  have eq3898 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3896 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3896
    | (have j0 := eq3896 X0 X1
       grind)
    | exact resolve eq3896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq4169 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3535
       have i₂ := eq1954 y x
       grind)
    | exact superpose eq1954 eq3535
    | (have j1 := eq1954 (σ y) (σ x)
       grind)
    | (have r₁ := eq3535
       have r₂ := eq1954 y x
       grind)
    | exact resolve eq3535 eq1954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq4170 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4169
  have eq4201 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144 (σ x) (σ y)
       have i₂ := eq4170
       grind)
    | exact superpose eq4170 eq144
    | (have r₁ := eq144 (σ x) (σ y)
       have r₂ := eq4170
       grind)
    | (have r₁ := eq144 x y
       have r₂ := eq4170
       grind)
    | exact resolve eq144 eq4170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq4170
  have eq4215 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4201
  have eq4222 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4215
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4215
    | exact resolve eq4215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215
  have eq4241 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq4222
       grind)
    | exact superpose eq4222 eq10
    | exact resolve eq10 eq4222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq4288 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4241
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4241
    | exact resolve eq4241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4311 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3898 x x
       have i₂ := eq4288
       grind)
    | exact superpose eq4288 eq3898
    | (have j0 := eq3898 x x
       grind)
    | (have r₁ := eq3898 x x
       have r₂ := eq4288
       grind)
    | exact resolve eq3898 eq4288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898 eq4288
  have eq4314 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4311
  have eq4355 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq125 y x
       have i₂ := eq4314
       grind)
    | exact superpose eq4314 eq125
    | exact resolve eq125 eq4314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4314
  have eq4371 : x = (M.op x x) := by grind
  clear eq4355
  have eq4391 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq4371
       grind)
    | exact superpose eq4371 eq73
    | exact resolve eq73 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq4428 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq694 x x x
       have i₂ := eq4371
       grind)
    | exact superpose eq4371 eq694
    | exact resolve eq694 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371
  have eq4437 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq4428 X0
       have i₂ := eq125 X0 x
       grind)
    | exact superpose eq125 eq4428
    | exact resolve eq4428 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq4428
  have eq5010 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4391 X0
       have i₂ := eq4437 X0
       grind)
    | exact superpose eq4437 eq4391
    | exact resolve eq4391 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391 eq4437
  have eq5017 : ∀ X0 : G, x ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq5010 X0
       grind)
    | exact superpose eq5010 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq5010 x
       grind)
    | exact resolve eq12 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5049 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X1 x X0
       have i₂ := eq5010 X0
       grind)
    | exact superpose eq5010 eq694
    | exact resolve eq694 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq5068 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq1684 X0 x
       have i₂ := eq5010 (τ X0)
       grind)
    | exact superpose eq5010 eq1684
    | exact resolve eq1684 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq5070 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq5068 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5068
    | (have j0 := eq5068 X0
       grind)
    | exact resolve eq5068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5075 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5049 X0 X0
       have i₂ := eq5010 X0
       grind)
    | exact superpose eq5010 eq5049
    | exact resolve eq5049 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq6335 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq5070 X0
       grind)
    | exact superpose eq5070 eq22
    | (have j1 := eq5070 X0
       grind)
    | exact resolve eq22 eq5070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5070
  have eq6348 : ∀ X0 : G, (τ X0) = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq6335 X0
       have j1 := eq5017 (τ X0)
       grind)
    | (have r₁ := eq6335 X0
       have r₂ := eq5017 (τ X0)
       grind)
    | exact resolve eq6335 eq5017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5017 eq6335
  have eq6352 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6348 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6348
    | exact resolve eq6348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq6392 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3535
       have i₂ := eq6352 y
       grind)
    | exact superpose eq6352 eq3535
    | exact resolve eq3535 eq6352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535 eq6352
  have eq6395 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6392
       have i₂ := eq5010 y
       grind)
    | exact superpose eq5010 eq6392
    | exact resolve eq6392 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392
  have eq6396 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6395
  have eq6552 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq6396
       grind)
    | exact superpose eq6396 eq9
    | exact resolve eq9 eq6396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6396
  have eq6611 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6552 X0
       have i₂ := eq5075 X0 (σ x)
       grind)
    | exact superpose eq5075 eq6552
    | exact resolve eq6552 eq5075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075 eq6552
  have eq6626 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6611 (σ y)
       grind)
    | exact superpose eq6611 eq16
    | exact resolve eq16 eq6611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6611
  have eq6685 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6626
       have i₂ := eq5010 y
       grind)
    | exact superpose eq5010 eq6626
    | exact resolve eq6626 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5010 eq6626
  have eq6686 : False := by grind
  exact eq6686

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq97 eq69
    | (have j0 := eq69 (σ y) x
       grind)
    | exact resolve eq69 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq745
    | exact resolve eq745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq749 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq746
       have r₂ := eq27
       grind)
    | exact resolve eq746 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq751 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq749 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq749
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq749
       grind)
    | exact resolve eq13 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq764 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq751
  have eq779 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq764 eq103
    | exact resolve eq103 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq764
  have eq783 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq779
    | exact resolve eq779 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq779
  have eq786 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq69 y y
       have i₂ := eq783
       grind)
    | exact superpose eq783 eq69
    | (have j0 := eq69 y x
       grind)
    | exact resolve eq69 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq787 : y = (M.op y y) := by grind
  clear eq786
  have eq790 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq787
       grind)
    | exact resolve eq13 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq14
    | exact resolve eq14 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq14
    | exact resolve eq14 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq803 : y = (k y y) := by grind
  clear eq790
  have eq818 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq803
       grind)
    | exact superpose eq803 eq76
    | exact resolve eq76 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq803
  have eq822 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq818
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq818
    | exact resolve eq818 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq825 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq822 eq69
    | (have j0 := eq69 (σ y) x
       grind)
    | exact resolve eq69 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq822
  have eq826 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq825
  have eq844 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq826 eq14
    | exact resolve eq14 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq883 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq792 (M.op y X0)
       have i₂ := eq791 X0
       grind)
    | exact superpose eq791 eq792
    | exact resolve eq792 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq791 X0
       have i₂ := eq883 X0
       grind)
    | exact superpose eq883 eq791
    | exact resolve eq791 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq883
  have eq968 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq792 X0
       have i₂ := eq951 X0
       grind)
    | exact superpose eq951 eq792
    | exact resolve eq792 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq979 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq951 X0
       have i₂ := eq968 X0
       grind)
    | exact superpose eq968 eq951
    | exact resolve eq951 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq988 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y X0
       have i₂ := eq968 X0
       grind)
    | exact superpose eq968 eq14
    | exact resolve eq14 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq988 X0 X1
       have i₂ := eq968 X1
       grind)
    | exact superpose eq968 eq988
    | exact resolve eq988 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1026 : y = (M.op x y) := by
    first
    | (have i₁ := eq979 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq979
    | (have j0 := eq979 x
       grind)
    | exact resolve eq979 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1092 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1026 eq20
    | exact resolve eq20 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1128 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1092
    | exact resolve eq1092 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1092
  have eq1151 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1128 eq26
    | exact resolve eq26 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1605 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq844 X0
       have i₂ := eq1009 X0 sF3
       grind)
    | exact superpose eq1009 eq844
    | exact resolve eq844 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq1009
  have eq1606 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1128 eq1605
    | exact resolve eq1605 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1605
  have eq1621 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op x (σ (M.op x y))) (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1606 eq218
    | exact resolve eq218 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq1606
  have eq1626 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op x (σ (M.op x y))) y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1026 eq1621
    | exact resolve eq1621 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq1621
  have eq1632 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op y X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1626 X0
       have i₂ := eq979 (M.op x sF1)
       grind)
    | exact superpose eq979 eq1626
    | exact resolve eq1626 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq1626
  have eq1635 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1632 X0
       have i₂ := eq968 X0
       grind)
    | exact superpose eq968 eq1632
    | exact resolve eq1632 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq1632
  have eq1780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1635 eq1151
    | exact resolve eq1151 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq1635
  have eq1791 : False := by grind
  exact eq1791

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq190 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq198 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq606 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq609 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq609 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq609 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq609 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq703 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq604
       grind)
    | exact superpose eq604 eq39
    | exact resolve eq39 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq778
    | exact resolve eq778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq781 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq779
    | exact resolve eq779 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq843 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq179 eq198
    | exact resolve eq198 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq863 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq843 X0
       grind)
    | exact superpose eq843 eq16
    | exact resolve eq16 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq863
    | exact resolve eq863 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq179 eq863
    | exact resolve eq863 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq917 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq180 eq863
    | exact resolve eq863 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq863
  have eq936 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq913 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq917 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq917 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq944
       have r₂ := eq947
       grind)
    | exact resolve eq944 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq781 eq606
    | exact resolve eq606 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1614 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1607
       have r₂ := eq27
       grind)
    | exact resolve eq1607 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1633 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1614 eq909
    | exact resolve eq909 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1637 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1614 eq843
    | exact resolve eq843 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1641 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1637
    | exact resolve eq1637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1690 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq843 y
       have i₂ := eq1641
       grind)
    | exact superpose eq1641 eq843
    | exact resolve eq843 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq1694 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1690
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1690
    | exact resolve eq1690 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1726 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1694 eq948
    | exact resolve eq948 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1730 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1726
       have r₂ := eq175
       grind)
    | exact resolve eq1726 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1911 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1730 eq141
    | exact resolve eq141 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1730
  have eq1919 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1911
    | exact resolve eq1911 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1922 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1919
       have r₂ := eq174
       grind)
    | exact resolve eq1919 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1919
  have eq1946 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1922 eq843
    | exact resolve eq843 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq1950 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1946
    | exact resolve eq1946 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946
  have eq1958 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq604
       have i₂ := eq1950
       grind)
    | exact superpose eq1950 eq604
    | exact resolve eq604 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq1960 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1950
       grind)
    | exact superpose eq1950 eq39
    | exact resolve eq39 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1950
  have eq1962 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1958
  have eq1965 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1960
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1960
    | exact resolve eq1960 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1971 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1965 eq606
    | exact resolve eq606 eq1965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1965
  have eq1976 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1971
  have eq2020 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq843 y
       have i₂ := eq1962
       grind)
    | exact superpose eq1962 eq843
    | exact resolve eq843 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq2024 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2020
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2020
    | exact resolve eq2020 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2025 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2024
  have eq2079 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1976 eq843
    | exact resolve eq843 eq1976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq2083 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2079
    | exact resolve eq2079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2084 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2083
  have eq2112 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2084 eq947
    | (have r₁ := eq947
       have r₂ := eq2084
       grind)
    | exact resolve eq947 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq2115 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2084
  have eq2118 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2112
       have r₂ := eq175
       grind)
    | exact resolve eq2112 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2112
  have eq2238 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1614 eq703
    | exact resolve eq703 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq2374 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2238
    | exact resolve eq2238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2375 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2374
  have eq2385 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq781 eq2375
    | exact resolve eq2375 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2391 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1633 eq2385
    | exact resolve eq2385 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633 eq2385
  have eq2547 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq909 y y
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq909
    | exact resolve eq909 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq2548 : (k y x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq703 y
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq703
    | exact resolve eq703 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq2552 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq843 y
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq843
    | exact resolve eq843 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2556 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2552
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2552
    | exact resolve eq2552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2558 : x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2548
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2548
    | exact resolve eq2548 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq2559 : x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2558
  have eq2564 : x = (M.op x y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2547 eq2559
    | exact resolve eq2559 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547 eq2559
  have eq2567 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2556 eq2564
    | exact resolve eq2564 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564
  have eq2597 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2556 eq2025
    | exact resolve eq2025 eq2556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556
  have eq2598 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2597
  have eq2640 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2598 eq31
    | exact resolve eq31 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq2738 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2640
    | exact resolve eq2640 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq2762 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2738 eq28
    | exact resolve eq28 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2738
  have eq2788 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2762
    | exact resolve eq2762 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq2789 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2788
  have eq2793 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2789
       grind)
    | exact superpose eq2789 eq24
    | exact resolve eq24 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq2835 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2793
    | exact resolve eq2793 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793
  have eq2890 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2567 eq37
    | exact resolve eq37 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq2901 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2890
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2890
    | exact resolve eq2890 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3012 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2901 eq687
    | (have j0 := eq687 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq687 (σ (M.op x y)) (σ x)
       have r₂ := eq2901
       grind)
    | exact resolve eq687 eq2901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq2901
  have eq3015 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3012
  have eq3016 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3015
  have eq3058 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3016 eq843
    | exact resolve eq843 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq3016
  have eq3096 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2835 eq3058
    | exact resolve eq3058 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058
  have eq3125 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq3096
  have eq3127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq3125
    | exact resolve eq3125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125
  have eq3128 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1694 eq3127
    | exact resolve eq3127 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694 eq3127
  have eq3129 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3128
  have eq3130 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3129 eq27
    | exact resolve eq27 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq3164 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2835 eq3130
    | (have r₁ := eq3130
       have r₂ := eq2835
       grind)
    | exact resolve eq3130 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835 eq3130
  have eq3167 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq3164
  have eq3168 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3167
  have eq3177 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3168 eq190
    | exact resolve eq190 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq3194 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3168 eq917
    | exact resolve eq917 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq3219 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3194 eq3177
    | exact resolve eq3177 eq3194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177 eq3194
  have eq3228 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq3219
    | exact resolve eq3219 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq3230 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2025 eq3228
    | exact resolve eq3228 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025 eq3228
  have eq3231 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq3230
  have eq3262 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3231 eq3168
    | exact resolve eq3168 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168 eq3231
  have eq3263 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3262
  have eq3276 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3263 eq31
    | exact resolve eq31 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3263
  have eq3366 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3276
    | exact resolve eq3276 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3276
  have eq3367 : x = (M.op x y) ∨ x = y := by grind
  clear eq3366
  have eq3381 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq3367
       grind)
    | exact superpose eq3367 eq18
    | exact resolve eq18 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3392 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq913
       have i₂ := eq3367
       grind)
    | exact superpose eq3367 eq913
    | exact resolve eq913 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq3860 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq3392 eq183
    | exact resolve eq183 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq3392
  have eq3890 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3381 eq3860
    | exact resolve eq3860 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq3860
  have eq3932 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq3890
  have eq3933 : x = y := by
    first
    | (have r₁ := eq3932
       have r₂ := eq3367
       grind)
    | exact resolve eq3932 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367 eq3932
  have eq3939 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq18
    | exact resolve eq18 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3940 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq24
    | exact resolve eq24 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3985 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3940
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3940
    | exact resolve eq3940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq3987 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3985 eq26
    | exact resolve eq26 eq3985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4012 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3985 eq781
    | exact resolve eq781 eq3985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq4035 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3985 eq2115
    | (have r₁ := eq2115
       have r₂ := eq3985
       grind)
    | exact resolve eq2115 eq3985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq4037 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3985 eq2118
    | (have r₁ := eq2118
       have r₂ := eq3985
       grind)
    | exact resolve eq2118 eq3985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq3985
  have eq4040 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4037
  have eq4041 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4035
  have eq4047 : x = (M.op x y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4040
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq4040
    | exact resolve eq4040 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq4049 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4041
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq4041
    | exact resolve eq4041 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4041
  have eq4071 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4012
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq4012
    | exact resolve eq4012 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933 eq4012
  have eq4088 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4071
       have i₂ := eq3939
       grind)
    | exact superpose eq3939 eq4071
    | exact resolve eq4071 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq4071
  have eq4089 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4088
  have eq4092 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4047 eq4089
    | exact resolve eq4089 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047 eq4089
  have eq4246 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4049 eq27
    | exact resolve eq27 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049
  have eq4304 : x = (M.op x y) := by
    first
    | (have r₁ := eq4246
       have r₂ := eq4092
       grind)
    | exact resolve eq4246 eq4092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092 eq4246
  have eq4313 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4304
       grind)
    | exact superpose eq4304 eq22
    | exact resolve eq22 eq4304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4325 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq936
       have i₂ := eq4304
       grind)
    | exact superpose eq4304 eq936
    | (have r₁ := eq936
       have r₂ := eq4304
       grind)
    | exact resolve eq936 eq4304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq4304
  have eq4331 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq4325
  have eq4349 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4313 eq20
    | exact resolve eq20 eq4313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq4471 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4331 eq37
    | exact resolve eq37 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4331
  have eq4486 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq4471
    | exact resolve eq4471 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4471
  have eq4488 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4349 eq4486
    | exact resolve eq4486 eq4349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4486
  have eq4498 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4488 eq659
    | (have j0 := eq659 (σ x) (σ x)
       grind)
    | (have r₁ := eq659 (σ x) (σ x)
       have r₂ := eq4488
       grind)
    | exact resolve eq659 eq4488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq4488
  have eq4499 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4498
  have eq4500 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4499
  have eq4514 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4500 eq3987
    | exact resolve eq3987 eq4500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987 eq4500
  have eq4573 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4514 eq27
    | exact resolve eq27 eq4514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4514
  have eq4619 : False := by grind
  exact eq4619

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq61
    | exact resolve eq61 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq681 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq680 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq680
    | (have j0 := eq680 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq680 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq680 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq680
    | (have j0 := eq680 (σ X0) (σ X1)
       grind)
    | exact resolve eq680 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq2307 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0) ≠ X4 ∨ (M.op X4 (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0)) = X4 ∨ (k (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq654 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq654
    | exact resolve eq654 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq654
  have eq20611 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1085 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq20613 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq20611 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20611
  have eq20681 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20613 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq20613
    | (have j0 := eq20613 (τ X0)
       grind)
    | exact resolve eq20613 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20613
  have eq20693 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20681 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20681
    | (have j0 := eq20681 X0
       grind)
    | exact resolve eq20681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20681
  have eq20704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20693 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20693
    | (have j0 := eq20693 X0
       grind)
    | exact resolve eq20693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20693
  have eq20720 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20704 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq20704
    | (have j0 := eq20704 (τ X0)
       grind)
    | exact resolve eq20704 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20704
  have eq20732 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20720 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20720
    | (have j0 := eq20720 X0
       grind)
    | exact resolve eq20720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20720
  have eq20743 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20732 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20732
    | (have j0 := eq20732 X0
       grind)
    | exact resolve eq20732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20732
  have eq21189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1084 x y
       grind)
    | exact superpose eq1084 eq16
    | (have j1 := eq1084 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1084 x y
       grind)
    | exact resolve eq16 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq21351 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq21189
  have eq26702 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) ≠ X0 ∨ (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X0) ∨ (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (k X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2307 X0 X1 X0 X3 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X3)) X0) X2)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X3)) X0) X2
       grind)
    | exact superpose eq9 eq2307
    | exact resolve eq2307 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq26709 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ X0 ∨ (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X0) ∨ (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (k X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26702 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq26702
    | (have j0 := eq26702 X0 X1 X2 X3
       grind)
    | exact resolve eq26702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26702
  have eq26723 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X3) X0) ∨ (M.op X0 X3) ≠ X0 ∨ (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (k X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26709 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq26709
    | (have j0 := eq26709 X0 X1 X2 X3
       grind)
    | exact resolve eq26709 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26709
  have eq26734 : ∀ X0 X3 : G, (M.op X0 X3) ≠ X0 ∨ (M.op X0 X3) = (M.op (M.op X0 X3) X0) ∨ (M.op X0 X3) = (k X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq26723 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq26723
    | (have j0 := eq26723 X0 x x X3
       grind)
    | exact resolve eq26723 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26723
  have eq36617 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26734 (σ y) (σ x)
       have i₂ := eq21351
       grind)
    | exact superpose eq21351 eq26734
    | (have r₁ := eq26734 (σ y) (σ x)
       have r₂ := eq21351
       grind)
    | (have r₁ := eq26734 (σ x) (σ y)
       have r₂ := eq21351
       grind)
    | (have r₁ := eq26734 y x
       have r₂ := eq21351
       grind)
    | exact resolve eq26734 eq21351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21351 eq26734
  have eq36624 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq36617
  have eq36637 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq20743 (σ y)
       grind)
    | (have r₁ := eq36624
       have r₂ := eq20743 (σ y)
       grind)
    | exact resolve eq36624 eq20743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20743 eq36624
  have eq84948 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq681 X0 X1
       grind)
    | exact superpose eq681 eq12
    | (have j0 := eq12 (τ X0) (τ X1)
       have j1 := eq681 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq681 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq681 X0 X1
       grind)
    | exact resolve eq12 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq85214 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84948 X0 X1
       have j1 := eq12 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq84948 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq84948 X0 X1
       have r₂ := eq12 (τ X0) (τ X1)
       grind)
    | exact resolve eq84948 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84948
  have eq85243 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85214 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq85214
    | (have j0 := eq85214 X0 X1
       grind)
    | exact resolve eq85214 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq85214
  have eq85741 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq85243 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85243
    | (have j0 := eq85243 (σ X0) (σ X1)
       grind)
    | exact resolve eq85243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85243
  have eq85802 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq85741 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq85741
    | (have j0 := eq85741 X0 X1
       grind)
    | exact resolve eq85741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85741
  have eq85830 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq85802 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq85802
    | (have j0 := eq85802 X0 X1
       grind)
    | exact resolve eq85802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85802
  have eq85853 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq85830 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85830
    | (have j0 := eq85830 X0 X1
       grind)
    | exact resolve eq85830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85830
  have eq85876 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq85853 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq85853
    | (have j0 := eq85853 X0 X1
       grind)
    | exact resolve eq85853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85853
  have eq85887 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85876 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq85876
    | (have j0 := eq85876 X0 X1
       grind)
    | exact resolve eq85876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85876
  have eq85898 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85887 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85887
    | (have j0 := eq85887 X0 X1
       grind)
    | exact resolve eq85887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85887
  have eq85927 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85898 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85898
    | (have j0 := eq85898 (σ X0) (σ X1)
       grind)
    | exact resolve eq85898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86877 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq36637
       grind)
    | exact superpose eq36637 eq12
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq36637
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq36637
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq36637
       grind)
    | exact resolve eq12 eq36637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36637
  have eq87066 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq86877
  have eq87138 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87066
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq87066
    | exact resolve eq87066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87066
  have eq87222 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 (σ x) (σ y)
       have i₂ := eq87138
       grind)
    | exact superpose eq87138 eq90
    | exact resolve eq90 eq87138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87138
  have eq87564 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq87222
       grind)
    | exact superpose eq87222 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq87222
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq87222
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq87222
       grind)
    | exact resolve eq12 eq87222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87222
  have eq87753 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq87564
  have eq87824 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87753
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq87753
    | exact resolve eq87753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87753
  have eq87896 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq87824
       grind)
    | exact superpose eq87824 eq10
    | exact resolve eq10 eq87824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87824
  have eq88058 : (σ x) = (σ (k x x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87896
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq87896
    | exact resolve eq87896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87896
  have eq88086 : (τ (σ x)) = (k x x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq88058
       grind)
    | exact superpose eq88058 eq10
    | exact resolve eq10 eq88058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88058
  have eq88248 : y = (k y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88086
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq88086
    | exact resolve eq88086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88086
  have eq88319 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85898 y y
       have i₂ := eq88248
       grind)
    | exact superpose eq88248 eq85898
    | (have j0 := eq85898 y y
       grind)
    | (have r₁ := eq85898 y y
       have r₂ := eq88248
       grind)
    | (have r₁ := eq85898 x x
       have r₂ := eq88248
       grind)
    | exact resolve eq85898 eq88248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88248
  have eq88323 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq88319
  have eq88324 : y = (M.op y y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq88323
  have eq88408 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq88324
       grind)
    | exact superpose eq88324 eq76
    | exact resolve eq76 eq88324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88507 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq443 y y x
       have i₂ := eq88324
       grind)
    | exact superpose eq88324 eq443
    | exact resolve eq443 eq88324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88324
  have eq88697 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq88507 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq88507
    | exact resolve eq88507 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88507
  have eq90485 : ∀ X0 : G, y = (M.op y x) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88697 eq88408
    | exact resolve eq88408 eq88697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88408 eq88697
  have eq90515 : ∀ X0 : G, y = (M.op y y) ∨ x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90 y x
       have i₂ := eq90485 X0
       grind)
    | exact superpose eq90485 eq90
    | (have j1 := eq90485 y
       grind)
    | exact resolve eq90 eq90485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90485
  have eq91423 : y ≠ y ∨ x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq90515 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90515
  have eq91424 : y = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq91423
  have eq91551 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq91424
       grind)
    | exact superpose eq91424 eq76
    | exact resolve eq76 eq91424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91650 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq443 y y x
       have i₂ := eq91424
       grind)
    | exact superpose eq91424 eq443
    | exact resolve eq443 eq91424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91424
  have eq91840 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq91650 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq91650
    | exact resolve eq91650 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91650
  have eq93183 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq91840 eq91551
    | exact resolve eq91551 eq91840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91551 eq91840
  have eq93248 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq85898 x x
       have i₂ := eq93183 X0
       grind)
    | exact superpose eq93183 eq85898
    | (have j0 := eq85898 x x
       have j1 := eq93183 X0
       grind)
    | (have r₁ := eq85898 x x
       have r₂ := eq93183 X0
       grind)
    | exact resolve eq85898 eq93183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85898 eq93183
  have eq93252 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq93248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93248
  have eq93253 : ∀ X0 : G, x = (M.op x y) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq93252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93252
  have eq95616 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq90 x y
       have i₂ := eq93253 X0
       grind)
    | exact superpose eq93253 eq90
    | (have j1 := eq93253 X0
       grind)
    | exact resolve eq90 eq93253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93253
  have eq95781 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq95616 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95616
  have eq96000 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq95781 X1
       grind)
    | exact superpose eq95781 eq76
    | (have j1 := eq95781 X1
       grind)
    | exact resolve eq76 eq95781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq96099 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq443 x x x
       have i₂ := eq95781 X0
       grind)
    | exact superpose eq95781 eq443
    | (have j1 := eq95781 X1
       grind)
    | exact resolve eq443 eq95781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95781
  have eq96288 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96099 X0 X1
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq96099
    | (have j0 := eq96099 X0 X1
       grind)
    | exact resolve eq96099 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq96099
  have eq97625 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq96288 eq96000
    | (have j0 := eq96000 X0 X1
       have j1 := eq96288 X0 X1
       grind)
    | exact resolve eq96000 eq96288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96000
  have eq97626 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq97625 eq96288
    | (have j0 := eq96288 X0 X1
       have j1 := eq97625 X0 X1
       grind)
    | exact resolve eq96288 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96288
  have eq97630 : ∀ X0 : G, y ≠ y ∨ y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 y
       have i₂ := eq97625 X0 y
       grind)
    | exact superpose eq97625 eq75
    | (have j1 := eq97625 X0 x
       grind)
    | (have r₁ := eq75 y
       have r₂ := eq97625 X0 y
       grind)
    | (have r₁ := eq75 x
       have r₂ := eq97625 x x
       grind)
    | exact resolve eq75 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97732 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443 y X1 X0
       have i₂ := eq97625 X2 X0
       grind)
    | exact superpose eq97625 eq443
    | (have j1 := eq97625 X2 X1
       grind)
    | exact resolve eq443 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq97909 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq97625 X1 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq97625 eq77
    | (have j1 := eq97625 X1 X1
       grind)
    | exact resolve eq77 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98111 : ∀ X0 : G, y = (k y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq97630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97630
  have eq98234 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq97625 eq97909
    | (have j0 := eq97909 X0 X1
       have j1 := eq97625 X1 X1
       grind)
    | exact resolve eq97909 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97909
  have eq98345 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq97625 eq97732
    | (have j0 := eq97732 X0 X1 X2
       have j1 := eq97625 X2 X1
       grind)
    | exact resolve eq97732 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97732
  have eq98489 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq97625 eq98234
    | (have j0 := eq98234 X0 X1
       have j1 := eq97625 X1 X1
       grind)
    | exact resolve eq98234 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98234
  have eq99586 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq97626 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97626
  have eq99587 : x = (M.op y x) := by grind
  clear eq99586
  have eq100656 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op y X0) x) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 y x X1
       have i₂ := eq99587
       grind)
    | exact superpose eq99587 eq61
    | exact resolve eq61 eq99587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99587
  have eq101412 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85927 y y
       have i₂ := eq98111 X0
       grind)
    | exact superpose eq98111 eq85927
    | (have j0 := eq85927 y y
       have j1 := eq98111 X0
       grind)
    | exact resolve eq85927 eq98111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98111
  have eq101413 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq101412 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101412
  have eq101414 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq101413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101413
  have eq102391 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq98489 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102392 : y = (M.op x y) := by grind
  clear eq102391
  have eq103447 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102392
       grind)
    | exact superpose eq102392 eq16
    | exact resolve eq16 eq102392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103456 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 x y X1
       have i₂ := eq102392
       grind)
    | exact superpose eq102392 eq61
    | exact resolve eq61 eq102392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq102392
  have eq110699 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq101414 X1
       grind)
    | exact superpose eq101414 eq9
    | (have j1 := eq101414 X1
       grind)
    | exact resolve eq9 eq101414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101414
  have eq110967 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq98345 eq110699
    | (have j0 := eq110699 X0 X1
       have j1 := eq98345 X0 X1 X1
       grind)
    | exact resolve eq110699 eq98345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98345 eq110699
  have eq113351 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) y) X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq103456 (σ y) X0
       have i₂ := eq110967 (M.op (M.op (M.op x (σ y)) y) X0) X1
       grind)
    | exact superpose eq110967 eq103456
    | (have j1 := eq110967 X0 X1
       grind)
    | exact resolve eq103456 eq110967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103456 eq110967
  have eq113593 : ∀ X0 X1 : G, (σ y) = (M.op (M.op y X0) (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq98489 eq113351
    | (have j0 := eq113351 X0 X1
       have j1 := eq98489 X0 X1
       grind)
    | exact resolve eq113351 eq98489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98489 eq113351
  have eq113601 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq97625 eq113593
    | (have j0 := eq113593 X0 X1
       have j1 := eq97625 X1 X1
       grind)
    | exact resolve eq113593 eq97625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97625 eq113593
  have eq117151 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq103447
       have i₂ := eq113601 (σ x) X0
       grind)
    | exact superpose eq113601 eq103447
    | (have j1 := eq113601 X0 X0
       grind)
    | (have r₁ := eq103447
       have r₂ := eq113601 (σ x) x
       grind)
    | exact resolve eq103447 eq113601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113601
  have eq117208 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq117151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117151
  have eq118156 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq117208 x
       grind)
    | exact superpose eq117208 eq75
    | (have r₁ := eq75 x
       have r₂ := eq117208 x
       grind)
    | exact resolve eq75 eq117208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq118436 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq77 x X0
       have i₂ := eq117208 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq117208 eq77
    | exact resolve eq77 eq117208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq118639 : x = (k x x) := by grind
  clear eq118156
  have eq118763 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq118436 X0
       have i₂ := eq117208 x
       grind)
    | exact superpose eq117208 eq118436
    | exact resolve eq118436 eq117208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118436
  have eq119021 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq118763 X0
       have i₂ := eq117208 X0
       grind)
    | exact superpose eq117208 eq118763
    | exact resolve eq118763 eq117208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118763
  have eq119252 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85927 x x
       have i₂ := eq118639
       grind)
    | exact superpose eq118639 eq85927
    | (have j0 := eq85927 x x
       grind)
    | exact resolve eq85927 eq118639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85927 eq118639
  have eq119253 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq119252
  have eq119254 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq119253
  have eq119304 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100656 X0 X1
       have i₂ := eq119021 (M.op y X0)
       grind)
    | exact superpose eq119021 eq100656
    | exact resolve eq100656 eq119021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100656 eq119021
  have eq120858 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119304 X0 X1
       have i₂ := eq117208 X1
       grind)
    | exact superpose eq117208 eq119304
    | exact resolve eq119304 eq117208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117208 eq119304
  have eq121806 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq119254
       grind)
    | exact superpose eq119254 eq9
    | exact resolve eq9 eq119254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119254
  have eq121994 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq121806 X0
       have i₂ := eq120858 (σ x) X0
       grind)
    | exact superpose eq120858 eq121806
    | exact resolve eq121806 eq120858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120858 eq121806
  have eq122061 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq103447
       have i₂ := eq121994 (σ y)
       grind)
    | exact superpose eq121994 eq103447
    | (have r₁ := eq103447
       have r₂ := eq121994 (σ y)
       grind)
    | exact resolve eq103447 eq121994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103447 eq121994
  have eq122304 : False := by grind
  exact eq122304

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
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
  have eq41 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq70 (M.op X0 X1)
       grind)
    | exact superpose eq70 eq51
    | exact resolve eq51 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq51
    | exact resolve eq51 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq79 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq70 X0
       grind)
    | exact resolve eq13 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq79 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X0)) X0
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq81
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq106 X0 X1
       grind)
    | exact resolve eq13 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq317 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (σ (k (M.op (τ X0) X1) X2)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq465 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq9
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq507 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq487 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq487
    | (have j0 := eq487 (τ X0)
       grind)
    | exact resolve eq487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq517 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq507 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq507
    | (have j0 := eq507 X0
       grind)
    | exact resolve eq507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq524 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq517 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq517
    | (have j0 := eq517 X0
       grind)
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq612 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1104 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq106 X0 X0
       grind)
    | exact superpose eq106 eq83
    | (have j0 := eq83 X0
       grind)
    | exact resolve eq83 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1170 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) X0) = X0 ∨ (k X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1 X0
       have i₂ := eq132 X0 (M.op X1 X0)
       grind)
    | exact superpose eq132 eq98
    | (have j1 := eq132 X0 (M.op X1 X0)
       grind)
    | exact resolve eq98 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1187 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       have j1 := eq132 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq132 X0 X1
       grind)
    | exact resolve eq12 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1230 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1170 X0 X1
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq1170
    | (have j0 := eq1170 X0 X1
       grind)
    | exact resolve eq1170 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1170
  have eq1433 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0 (M.op X0 X1)
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq1230
    | (have j0 := eq1230 X0 X1
       have j1 := eq132 X0 (M.op X0 X1)
       grind)
    | exact resolve eq1230 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1230
  have eq1459 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X0 X1
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq1433
    | (have j0 := eq1433 X0 X1
       grind)
    | exact resolve eq1433 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq1460 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1459 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1665 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1669 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1665 X0 X1
       have j1 := eq1460 X0 X1
       grind)
    | (have r₁ := eq1665 X0 X1
       have r₂ := eq1460 X0 X1
       grind)
    | exact resolve eq1665 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460 eq1665
  have eq1683 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1669 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq1669
    | exact resolve eq1669 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1699 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq1669 (σ X0) X1
       grind)
    | exact superpose eq1669 eq28
    | exact resolve eq28 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1702 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) X1)
       have i₂ := eq1669 (τ X0) X1
       grind)
    | exact superpose eq1669 eq17
    | exact resolve eq17 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1711 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1702 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1702
    | exact resolve eq1702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq1714 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1699 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1699
    | exact resolve eq1699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq1723 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1683 (σ X0)
       grind)
    | exact superpose eq1683 eq22
    | exact resolve eq22 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1683
  have eq1787 : ∀ X0 X1 : G, (k X0 (τ (σ (k X0 X1)))) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1714 X0 (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq1714
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq1714 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1820 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1787 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1787
    | (have j0 := eq1787 X0 X1
       grind)
    | exact resolve eq1787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq2225 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1723 x
       have i₂ := eq84 x x
       grind)
    | exact superpose eq84 eq1723
    | (have j1 := eq84 X0 X0
       grind)
    | exact resolve eq1723 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1723
  have eq2243 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2254 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2243 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq2243
    | (have j0 := eq2243 X0
       grind)
    | exact resolve eq2243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq5761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq465
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq465
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq465 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq5762 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq5761
  have eq5930 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq467
    | (have j0 := eq467 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq467 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq6022 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5930 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5930
    | (have j0 := eq5930 X0 X1 X2
       grind)
    | exact resolve eq5930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq6037 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6022 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6022
    | (have j0 := eq6022 X0 X1 X2
       grind)
    | exact resolve eq6022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6022
  have eq6044 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6037 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6037
    | (have j0 := eq6037 X0 X1 X2
       grind)
    | exact resolve eq6037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6037
  have eq6045 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6044 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6044
    | (have j0 := eq6044 X0 X1 X2
       grind)
    | exact resolve eq6044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6044
  have eq6046 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6045 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6045
    | (have j0 := eq6045 X0 X1 X2
       grind)
    | exact resolve eq6045 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6045
  have eq6047 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6046 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6046
    | (have j0 := eq6046 X0 X1 X2
       grind)
    | exact resolve eq6046 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6046
  have eq7348 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq2254 (τ X0)
       grind)
    | exact superpose eq2254 eq18
    | (have j1 := eq2254 (τ X0)
       grind)
    | exact resolve eq18 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2254
  have eq7358 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7348 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq7348
    | (have j0 := eq7348 X0
       grind)
    | exact resolve eq7348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq7348
  have eq7378 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7358 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7358
    | (have j0 := eq7358 X0
       grind)
    | exact resolve eq7358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7358
  have eq7395 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7378 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7378
    | (have j0 := eq7378 X0
       grind)
    | exact resolve eq7378 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7378
  have eq56009 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1714 y (σ x)
       have i₂ := eq5762
       grind)
    | exact superpose eq5762 eq1714
    | exact resolve eq1714 eq5762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5762
  have eq56202 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq56009
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq56009
    | exact resolve eq56009 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56009
  have eq60485 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (k X0 X1)
       have i₂ := eq6047 X0 X1 X0
       grind)
    | exact superpose eq6047 eq81
    | (have j1 := eq6047 X0 X1 x
       grind)
    | exact resolve eq81 eq6047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047
  have eq64678 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (k X0 (σ (τ X0))) (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0 (τ X0) (τ X0)
       have i₂ := eq1104 (τ X0)
       grind)
    | exact superpose eq1104 eq317
    | (have j0 := eq317 X0 (τ X0) x
       have j1 := eq1104 (τ X0)
       grind)
    | exact resolve eq317 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq1104
  have eq64866 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (k X0 (σ (τ X0))) (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq64678 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64678
  have eq64895 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq64866 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64866
    | (have j0 := eq64866 X0
       grind)
    | exact resolve eq64866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64866
  have eq65104 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (σ X0) (σ X0)
       have i₂ := eq64895 (σ X0)
       grind)
    | exact superpose eq64895 eq41
    | (have j1 := eq64895 (σ X0)
       grind)
    | exact resolve eq41 eq64895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq64895
  have eq65237 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (σ (M.op X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq65104 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65104
    | (have j0 := eq65104 X0
       grind)
    | exact resolve eq65104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65104
  have eq65329 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq65237 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq65237
    | (have j0 := eq65237 X0
       grind)
    | exact resolve eq65237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65237
  have eq65372 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65329 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65329
    | (have j0 := eq65329 X0
       grind)
    | exact resolve eq65329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65329
  have eq65457 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7395 X0
       have i₂ := eq65372 X0
       grind)
    | exact superpose eq65372 eq7395
    | (have j0 := eq7395 X0
       have j1 := eq65372 X0
       grind)
    | exact resolve eq7395 eq65372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7395 eq65372
  have eq65609 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq65457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65457
  have eq65680 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65609 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq65609 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq65609 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65609
  have eq65952 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65680 (σ X0)
       grind)
    | exact superpose eq65680 eq15
    | exact resolve eq15 eq65680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65968 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq65680 (τ X0)
       grind)
    | exact superpose eq65680 eq31
    | exact resolve eq31 eq65680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq66044 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65968 X0
       have i₂ := eq65680 X0
       grind)
    | exact superpose eq65680 eq65968
    | exact resolve eq65968 eq65680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65968
  have eq66058 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65952 X0
       have i₂ := eq65680 X0
       grind)
    | exact superpose eq65680 eq65952
    | exact resolve eq65952 eq65680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65952
  have eq66321 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (τ X0) X1
       have i₂ := eq66044 X0
       grind)
    | exact superpose eq66044 eq81
    | exact resolve eq81 eq66044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66434 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq612 (τ X0) (τ X0) x
       have i₂ := eq66044 X0
       grind)
    | exact superpose eq66044 eq612
    | exact resolve eq612 eq66044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66044
  have eq66750 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) X1
       have i₂ := eq66058 X0
       grind)
    | exact superpose eq66058 eq81
    | exact resolve eq81 eq66058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66806 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq66058 X0
       grind)
    | exact superpose eq66058 eq9
    | exact resolve eq9 eq66058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66863 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq612 (σ X0) (σ X0) x
       have i₂ := eq66058 X0
       grind)
    | exact superpose eq66058 eq612
    | exact resolve eq612 eq66058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66806 (σ X0) X1
       have i₂ := eq66058 X0
       grind)
    | exact superpose eq66058 eq66806
    | exact resolve eq66806 eq66058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66058 eq66806
  have eq400376 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k X1 (k X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1714 X0 (σ X1)
       have i₂ := eq1820 X1 X0
       grind)
    | exact superpose eq1820 eq1714
    | (have j1 := eq1820 X1 X0
       grind)
    | exact resolve eq1714 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq401501 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k X1 (k X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq400376 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq400376
    | (have j0 := eq400376 X0 X1
       grind)
    | exact resolve eq400376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400376
  have eq401637 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 (k X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq401501 X0 X1
       have i₂ := eq65680 X0
       grind)
    | exact superpose eq65680 eq401501
    | (have j0 := eq401501 X0 X1
       grind)
    | exact resolve eq401501 eq65680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401501
  have eq401981 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) ∨ x = (k x (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq401637 y x
       grind)
    | exact superpose eq401637 eq16
    | (have j1 := eq401637 y x
       grind)
    | exact resolve eq16 eq401637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401637
  have eq452686 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq56202
       have i₂ := eq65680 y
       grind)
    | exact superpose eq65680 eq56202
    | exact resolve eq56202 eq65680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56202 eq65680
  have eq455572 : x = (k x (τ (σ y))) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1714 x (σ y)
       have i₂ := eq452686
       grind)
    | exact superpose eq452686 eq1714
    | exact resolve eq1714 eq452686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq452686
  have eq456104 : x = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq455572
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq455572
    | exact resolve eq455572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455572
  have eq456119 : y = (M.op y y) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq456104
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq456104
       have r₂ := eq13 x y
       grind)
    | exact resolve eq456104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456104
  have eq457644 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq81 y X0
       have i₂ := eq456119
       grind)
    | exact superpose eq456119 eq81
    | exact resolve eq81 eq456119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457957 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq612 y y x
       have i₂ := eq456119
       grind)
    | exact superpose eq456119 eq612
    | exact resolve eq612 eq456119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456119
  have eq458486 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq457957 X0
       have i₂ := eq106 y X0
       grind)
    | exact superpose eq106 eq457957
    | exact resolve eq457957 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457957
  have eq461828 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k x y) ∨ y = (M.op y x) ∨ x = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq457644 X0
       have i₂ := eq458486 X0
       grind)
    | exact superpose eq458486 eq457644
    | exact resolve eq457644 eq458486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457644 eq458486
  have eq462464 : ∀ X0 : G, y = (M.op y x) ∨ x = (k x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq461828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461828
  have eq462538 : ∀ X0 : G, y = (M.op y y) ∨ x = (k x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq106 y x
       have i₂ := eq462464 X0
       grind)
    | exact superpose eq462464 eq106
    | (have j1 := eq462464 y
       grind)
    | exact resolve eq106 eq462464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462464
  have eq463860 : y ≠ y ∨ x = (k x y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq462538 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462538
  have eq463861 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq463860
  have eq464251 : ∀ X0 : G, (M.op (M.op (M.op (τ y) X0) (τ y)) X0) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq66321 y X0
       have i₂ := eq463861
       grind)
    | exact superpose eq463861 eq66321
    | exact resolve eq66321 eq463861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464285 : ∀ X0 : G, (τ y) = (M.op (M.op (τ y) (M.op (τ y) X0)) (τ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq66434 y x
       have i₂ := eq463861
       grind)
    | exact superpose eq463861 eq66434
    | exact resolve eq66434 eq463861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66434 eq463861
  have eq465106 : ∀ X0 : G, (τ y) = (M.op (M.op (τ y) X0) (τ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq464285 X0
       have i₂ := eq106 (τ y) X0
       grind)
    | exact superpose eq106 eq464285
    | exact resolve eq464285 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464285
  have eq472346 : ∀ X0 : G, (M.op (τ y) X0) = X0 ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq464251 X0
       have i₂ := eq465106 X0
       grind)
    | exact superpose eq465106 eq464251
    | exact resolve eq464251 eq465106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464251
  have eq472992 : ∀ X0 : G, (M.op (τ y) X0) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq472346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472346
  have eq473076 : ∀ X0 : G, (τ y) = (M.op X0 (τ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq465106 X0
       have i₂ := eq472992 X0
       grind)
    | exact superpose eq472992 eq465106
    | exact resolve eq465106 eq472992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465106 eq472992
  have eq474440 : ∀ X0 : G, (τ y) = (M.op X0 (τ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq473076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473076
  have eq478149 : ∀ X0 : G, (k X0 (σ (τ y))) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq1711 X0 (τ y)
       have i₂ := eq474440 (τ X0)
       grind)
    | exact superpose eq474440 eq1711
    | exact resolve eq1711 eq474440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711 eq474440
  have eq478312 : ∀ X0 : G, x = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq478149 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq478149
    | exact resolve eq478149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478149
  have eq478605 : x ≠ x ∨ x = (k x y) := by
    first
    | (have j0 := eq478312 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478312
  have eq478606 : x = (k x y) := by grind
  clear eq478605
  have eq478669 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq60485 x y
       have i₂ := eq478606
       grind)
    | exact superpose eq478606 eq60485
    | (have j0 := eq60485 x y
       grind)
    | exact resolve eq60485 eq478606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60485
  have eq491952 : y ≠ y ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq478669
       grind)
    | exact superpose eq478669 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq478669
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq478669
       grind)
    | exact resolve eq12 eq478669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478669
  have eq492406 : (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq491952
  have eq492613 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq492406
       have i₂ := eq478606
       grind)
    | exact superpose eq478606 eq492406
    | exact resolve eq492406 eq478606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492406
  have eq492614 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq492613
  have eq492633 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ x = (k x (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq401981
       have i₂ := eq492614
       grind)
    | exact superpose eq492614 eq401981
    | exact resolve eq401981 eq492614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401981 eq492614
  have eq493085 : y = (M.op y y) ∨ x = (k x (k x y)) ∨ x = (M.op x x) := by grind
  clear eq492633
  have eq493092 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq493085
       have i₂ := eq478606
       grind)
    | exact superpose eq478606 eq493085
    | exact resolve eq493085 eq478606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478606 eq493085
  have eq493096 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq524 y
       grind)
    | (have r₁ := eq493092
       have r₂ := eq524 x
       grind)
    | exact resolve eq493092 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq493092
  have eq493107 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 y X0
       have i₂ := eq493096
       grind)
    | exact superpose eq493096 eq81
    | exact resolve eq81 eq493096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493215 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq66750 y X0
       have i₂ := eq493096
       grind)
    | exact superpose eq493096 eq66750
    | exact resolve eq66750 eq493096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66750
  have eq493249 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq66863 y x
       have i₂ := eq493096
       grind)
    | exact superpose eq493096 eq66863
    | exact resolve eq66863 eq493096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66863
  have eq493420 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq612 y y x
       have i₂ := eq493096
       grind)
    | exact superpose eq493096 eq612
    | exact resolve eq612 eq493096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493096
  have eq493957 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq493420 X0
       have i₂ := eq106 y X0
       grind)
    | exact superpose eq106 eq493420
    | exact resolve eq493420 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493420
  have eq494007 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq493249 X0
       have i₂ := eq106 (σ y) X0
       grind)
    | exact superpose eq106 eq493249
    | exact resolve eq493249 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493249
  have eq500371 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq493107 X0
       have i₂ := eq493957 X0
       grind)
    | exact superpose eq493957 eq493107
    | exact resolve eq493107 eq493957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493107 eq493957
  have eq501018 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq500371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500371
  have eq501070 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 x X0
       have i₂ := eq501018 X1
       grind)
    | exact superpose eq501018 eq81
    | (have j1 := eq501018 X1
       grind)
    | exact resolve eq81 eq501018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501383 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq612 x x x
       have i₂ := eq501018 X0
       grind)
    | exact superpose eq501018 eq612
    | (have j1 := eq501018 X1
       grind)
    | exact resolve eq612 eq501018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501018
  have eq501920 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq501383 X0 X1
       have i₂ := eq106 x X0
       grind)
    | exact superpose eq106 eq501383
    | (have j0 := eq501383 X0 X1
       grind)
    | exact resolve eq501383 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501383
  have eq505173 : ∀ X0 X1 X2 : G, (M.op y X2) = X2 ∨ (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq501070 X0 X2
       have i₂ := eq501920 X0 X1
       grind)
    | exact superpose eq501920 eq501070
    | (have j0 := eq501070 X0 X2
       have j1 := eq501920 X0 X2
       grind)
    | exact resolve eq501070 eq501920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501070 eq501920
  have eq535583 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq505173 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505173
  have eq535584 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq535583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535583
  have eq535727 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 y X0
       have i₂ := eq535584 y X1
       grind)
    | exact superpose eq535584 eq82
    | (have j1 := eq535584 X0 X1
       grind)
    | exact resolve eq82 eq535584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq537200 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq535727 X0 X1
       have i₂ := eq106 y X0
       grind)
    | exact superpose eq106 eq535727
    | (have j0 := eq535727 X0 X1
       grind)
    | exact resolve eq535727 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535727
  have eq542710 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537200 X0 X1
       have i₂ := eq535584 X0 X2
       grind)
    | exact superpose eq535584 eq537200
    | (have j0 := eq537200 X0 X1
       have j1 := eq535584 X0 X1
       grind)
    | exact resolve eq537200 eq535584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535584 eq537200
  have eq701037 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq542710 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542710
  have eq701038 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq701037 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701037
  have eq703812 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq701038 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701038
  have eq703813 : y = (M.op x y) := by grind
  clear eq703812
  have eq1060999 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq493215 X0
       have i₂ := eq494007 X0
       grind)
    | exact superpose eq494007 eq493215
    | exact resolve eq493215 eq494007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493215
  have eq1062124 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1060999 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060999
  have eq1062187 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq494007 X0
       have i₂ := eq1062124 X0
       grind)
    | exact superpose eq1062124 eq494007
    | exact resolve eq494007 eq1062124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494007 eq1062124
  have eq1064589 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1062187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062187
  have eq1069311 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1064589 (σ x)
       grind)
    | exact superpose eq1064589 eq16
    | exact resolve eq16 eq1064589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064589
  have eq1069738 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1069311
       have i₂ := eq703813
       grind)
    | exact superpose eq703813 eq1069311
    | exact resolve eq1069311 eq703813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069311
  have eq1069739 : x = (M.op x x) := by grind
  clear eq1069738
  have eq1069971 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81 x X0
       have i₂ := eq1069739
       grind)
    | exact superpose eq1069739 eq81
    | exact resolve eq81 eq1069739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1070038 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66321 x X0
       have i₂ := eq1069739
       grind)
    | exact superpose eq1069739 eq66321
    | exact resolve eq66321 eq1069739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66321
  have eq1070293 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq612 x x x
       have i₂ := eq1069739
       grind)
    | exact superpose eq1069739 eq612
    | exact resolve eq612 eq1069739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069739
  have eq1071310 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1070293 X0
       have i₂ := eq106 x X0
       grind)
    | exact superpose eq106 eq1070293
    | exact resolve eq1070293 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1070293
  have eq1073437 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1069971 X0
       have i₂ := eq1071310 X0
       grind)
    | exact superpose eq1071310 eq1069971
    | exact resolve eq1069971 eq1071310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069971 eq1071310
  have eq1073819 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq612 x X1 X0
       have i₂ := eq1073437 X0
       grind)
    | exact superpose eq1073437 eq612
    | exact resolve eq612 eq1073437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq1076936 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1073819 X0 X0
       have i₂ := eq1073437 X0
       grind)
    | exact superpose eq1073437 eq1073819
    | exact resolve eq1073819 eq1073437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073437 eq1073819
  have eq1204401 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1070038 X0
       have i₂ := eq1076936 X0 (τ x)
       grind)
    | exact superpose eq1076936 eq1070038
    | exact resolve eq1070038 eq1076936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070038
  have eq1204638 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71217 (τ x) X0
       have i₂ := eq1204401 (τ x)
       grind)
    | exact superpose eq1204401 eq71217
    | exact resolve eq71217 eq1204401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71217 eq1204401
  have eq1207468 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1204638 X0
       have i₂ := eq1076936 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq1076936 eq1204638
    | exact resolve eq1204638 eq1076936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076936 eq1204638
  have eq1207809 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1207468 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq1207468
    | exact resolve eq1207468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207468
  have eq1208283 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1207809 (σ y)
       grind)
    | exact superpose eq1207809 eq16
    | exact resolve eq16 eq1207809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207809
  have eq1211376 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1208283
       have i₂ := eq703813
       grind)
    | exact superpose eq703813 eq1208283
    | exact resolve eq1208283 eq703813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703813 eq1208283
  have eq1211377 : False := by grind
  exact eq1211377

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X0 X0) X0 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq62
    | exact resolve eq62 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq81 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq9
    | exact resolve eq9 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq81
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq250 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) ≠ X0 ∨ (k X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0)
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq12
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq476 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq7665 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq711
    | (have j0 := eq711 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq711 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20207 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 (M.op X1 x) X1 x x
       have i₂ := eq73 (M.op X1 x)
       grind)
    | exact superpose eq73 eq250
    | exact resolve eq250 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq28089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7665 x y
       grind)
    | exact superpose eq7665 eq16
    | (have j1 := eq7665 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq7665 x y
       grind)
    | exact resolve eq16 eq7665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28094 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 (σ X0)
       have i₂ := eq7665 X0 X0
       grind)
    | exact superpose eq7665 eq73
    | (have j1 := eq7665 X0 X0
       grind)
    | exact resolve eq73 eq7665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7665
  have eq28260 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28094
  have eq28262 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq28089
  have eq48769 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq28262
       grind)
    | exact superpose eq28262 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq28262
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28262
       grind)
    | exact resolve eq12 eq28262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48875 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq20207 (σ y) (σ x)
       have i₂ := eq28262
       grind)
    | exact superpose eq28262 eq20207
    | exact resolve eq20207 eq28262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20207
  have eq48889 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq48769
  have eq48896 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq48875
       have r₂ := eq28262
       grind)
    | exact resolve eq48875 eq28262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48875
  have eq48953 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48889
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48889
    | exact resolve eq48889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48889
  have eq48961 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28262 eq48896
    | exact resolve eq48896 eq28262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28262 eq48896
  have eq48972 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14 eq48953
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq48953 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48953
  have eq48974 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48961
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq48961
    | exact resolve eq48961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48961
  have eq183012 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq103 (σ y)
       have i₂ := eq48972
       grind)
    | exact superpose eq48972 eq103
    | exact resolve eq103 eq48972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq48972
  have eq183296 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq183012
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq183012
    | exact resolve eq183012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183012
  have eq183312 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14 eq183296
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq183296 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183296
  have eq183313 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq183312
  have eq183326 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq183313
       grind)
    | exact superpose eq183313 eq10
    | exact resolve eq10 eq183313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183313
  have eq183495 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183326
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq183326
    | exact resolve eq183326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183326
  have eq183496 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq183495
       grind)
    | exact superpose eq183495 eq9
    | exact resolve eq9 eq183495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183783 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq183496 X0
       have i₂ := eq95 y X0
       grind)
    | exact superpose eq95 eq183496
    | exact resolve eq183496 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183496
  have eq184957 : (M.op y x) = (M.op x (M.op y x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119 x y
       have i₂ := eq183783 x
       grind)
    | exact superpose eq183783 eq119
    | exact resolve eq119 eq183783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq183783
  have eq185370 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183495 eq184957
    | exact resolve eq184957 eq183495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183495 eq184957
  have eq185371 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq185370
  have eq189170 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73 (σ y)
       have i₂ := eq48974
       grind)
    | exact superpose eq48974 eq73
    | exact resolve eq73 eq48974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189263 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq113 (σ y) (σ y)
       have i₂ := eq48974
       grind)
    | exact superpose eq48974 eq113
    | (have r₁ := eq113 y x
       have r₂ := eq48974
       grind)
    | exact resolve eq113 eq48974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48974
  have eq189456 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq189263
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq189263
    | exact resolve eq189263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189263
  have eq189474 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14 eq189456
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq189456 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189456
  have eq211884 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189170
       grind)
    | exact superpose eq189170 eq16
    | exact resolve eq16 eq189170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189170
  have eq212114 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq211884
       have i₂ := eq185371
       grind)
    | exact superpose eq185371 eq211884
    | exact resolve eq211884 eq185371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185371
  have eq212115 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq212114
  have eq212116 : (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq212115
  have eq212121 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq212116 eq211884
    | exact resolve eq211884 eq212116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211884
  have eq212323 : (σ y) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq189474 eq212116 eq212121
  have eq212335 : (τ (σ y)) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq212323
       grind)
    | exact superpose eq212323 eq10
    | exact resolve eq10 eq212323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212323
  have eq212514 : y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq212335
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq212335
    | exact resolve eq212335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212335
  have eq212614 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq212514
       grind)
    | exact superpose eq212514 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq212514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212514
  have eq212615 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq212614
  have eq212672 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq81 y X0
       have i₂ := eq212615
       grind)
    | exact superpose eq212615 eq81
    | exact resolve eq81 eq212615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212777 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq476 y y x
       have i₂ := eq212615
       grind)
    | exact superpose eq212615 eq476
    | exact resolve eq476 eq212615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212615
  have eq212981 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq212777 X0
       have i₂ := eq95 y X0
       grind)
    | exact superpose eq95 eq212777
    | exact resolve eq212777 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212777
  have eq214243 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq212981 eq212672
    | exact resolve eq212672 eq212981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212672
  have eq214244 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq214243 eq212981
    | exact resolve eq212981 eq214243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212981
  have eq214272 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 y x
       have i₂ := eq214243 X0
       grind)
    | exact superpose eq214243 eq95
    | (have j1 := eq214243 y
       grind)
    | exact resolve eq95 eq214243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214243
  have eq215145 : y ≠ y ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq214272 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214272
  have eq215146 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq215145
  have eq215257 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq81 y X0
       have i₂ := eq215146
       grind)
    | exact superpose eq215146 eq81
    | exact resolve eq81 eq215146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq215339 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq113 y y
       have i₂ := eq215146
       grind)
    | exact superpose eq215146 eq113
    | (have r₁ := eq113 y y
       have r₂ := eq215146
       grind)
    | exact resolve eq113 eq215146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215362 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq476 y y x
       have i₂ := eq215146
       grind)
    | exact superpose eq215146 eq476
    | exact resolve eq476 eq215146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq215515 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq215146
  have eq215517 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq215339
  have eq215566 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq215362 X0
       have i₂ := eq95 y X0
       grind)
    | exact superpose eq95 eq215362
    | exact resolve eq215362 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215362
  have eq215716 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq711 y y
       have i₂ := eq215517
       grind)
    | exact superpose eq215517 eq711
    | (have j0 := eq711 y y
       grind)
    | exact resolve eq711 eq215517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215517
  have eq215719 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq215716
  have eq216946 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq215566 eq215257
    | exact resolve eq215257 eq215566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215257 eq215566
  have eq216951 : ∀ X0 : G, x = y ∨ x = (M.op y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq216946 eq214244
    | (have j0 := eq214244 X0
       grind)
    | exact resolve eq214244 eq216946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214244
  have eq217045 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 y y
       have i₂ := eq216946 X0
       grind)
    | exact superpose eq216946 eq95
    | (have j1 := eq216946 x
       grind)
    | exact resolve eq95 eq216946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq217239 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq216951 X0
       grind)
    | (have r₁ := eq216951 X0
       have r₂ := eq215515
       grind)
    | exact resolve eq216951 eq215515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215515 eq216951
  have eq217522 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq78 y X0 X1
       have i₂ := eq217239 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq217239 eq78
    | exact resolve eq78 eq217239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq218681 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq216946 eq217522
    | exact resolve eq217522 eq216946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216946 eq217522
  have eq219224 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq218681 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218681
  have eq219875 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq217045 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217045
  have eq219876 : x = (M.op y x) := by grind
  clear eq219875
  have eq219909 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq219876
       grind)
    | exact superpose eq219876 eq12
    | exact resolve eq12 eq219876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219876
  have eq221394 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq219224 X1 X0
       grind)
    | exact superpose eq219224 eq9
    | exact resolve eq9 eq219224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230384 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq221394 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221394
  have eq230697 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq230384 (σ y) (σ y) X0
       have i₂ := eq215719
       grind)
    | exact superpose eq215719 eq230384
    | exact resolve eq230384 eq215719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215719 eq230384
  have eq231560 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq230697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230697
  have eq231583 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq219224 eq231560
    | exact resolve eq231560 eq219224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231560
  have eq232581 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq219224 X0 (σ y)
       have i₂ := eq231583 X0
       grind)
    | exact superpose eq231583 eq219224
    | exact resolve eq219224 eq231583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219224 eq231583
  have eq232815 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq232581 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232581
  have eq235367 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232815 (σ x)
       grind)
    | exact superpose eq232815 eq16
    | exact resolve eq16 eq232815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232815
  have eq235438 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq217239 eq235367
    | exact resolve eq235367 eq217239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217239 eq235367
  have eq235439 : x = (M.op y y) := by grind
  clear eq235438
  have eq235905 : y = (M.op x y) := by
    first
    | (have i₁ := eq73 y
       have i₂ := eq235439
       grind)
    | exact superpose eq235439 eq73
    | exact resolve eq73 eq235439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq235964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28260 y
       have i₂ := eq235439
       grind)
    | exact superpose eq235439 eq28260
    | (have j0 := eq28260 y
       grind)
    | exact resolve eq28260 eq235439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28260
  have eq236235 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235905
       grind)
    | exact superpose eq235905 eq16
    | exact resolve eq16 eq235905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235905
  have eq243033 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq236235
       have r₂ := eq235964
       grind)
    | exact resolve eq236235 eq235964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235964
  have eq243125 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq113 (σ y) (σ y)
       have i₂ := eq243033
       grind)
    | exact superpose eq243033 eq113
    | (have r₁ := eq113 (σ y) (σ y)
       have r₂ := eq243033
       grind)
    | exact resolve eq113 eq243033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq243033
  have eq243302 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq243125
  have eq243364 : (σ y) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq243302
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq243302
    | exact resolve eq243302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243302
  have eq243425 : (τ (σ y)) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq243364
       grind)
    | exact superpose eq243364 eq10
    | exact resolve eq10 eq243364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243364
  have eq243605 : y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq243425
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq243425
    | exact resolve eq243425 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243425
  have eq243707 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq243605
       grind)
    | exact superpose eq243605 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq243605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243605
  have eq243708 : y = (M.op y y) ∨ x = y := by grind
  clear eq243707
  have eq243724 : x = y ∨ x = y := by
    first
    | (have i₁ := eq243708
       have i₂ := eq235439
       grind)
    | exact superpose eq235439 eq243708
    | exact resolve eq243708 eq235439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235439 eq243708
  have eq243725 : x = y := by grind
  clear eq243724
  have eq243807 : x ≠ x ∨ x = (k x y) := by
    first
    | (have i₁ := eq219909
       have i₂ := eq243725
       grind)
    | exact superpose eq243725 eq219909
    | (have r₁ := eq219909
       have r₂ := eq243725
       grind)
    | exact resolve eq219909 eq243725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219909
  have eq243845 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq236235
       have i₂ := eq243725
       grind)
    | exact superpose eq243725 eq236235
    | exact resolve eq236235 eq243725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236235
  have eq243851 : x = (k x y) := by grind
  clear eq243807
  have eq243868 : x = (k x x) := by
    first
    | (have i₁ := eq243851
       have i₂ := eq243725
       grind)
    | exact superpose eq243725 eq243851
    | exact resolve eq243851 eq243725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243725 eq243851
  have eq244336 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq711 x x
       have i₂ := eq243868
       grind)
    | exact superpose eq243868 eq711
    | (have j0 := eq711 x x
       grind)
    | exact resolve eq711 eq243868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq243868
  have eq244339 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq244336
  have eq244354 : False := by grind
  exact eq244354
