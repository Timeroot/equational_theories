import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq180 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq276 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq278 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq281 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | (have j0 := eq278 X0
       grind)
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq287 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq281 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq281
    | (have j0 := eq281 (τ X0)
       grind)
    | exact resolve eq281 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq406 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X1 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq440 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq406
    | (have j0 := eq406 X0 X1
       grind)
    | exact resolve eq406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq1204 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1205 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1411 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1412 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1411 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq2236 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1205 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1205
    | exact resolve eq1205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq2274 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2236 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2236
    | (have j0 := eq2236 X0 X1
       grind)
    | exact resolve eq2236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2275 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2274 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2274
    | (have j0 := eq2274 X0 X1
       grind)
    | exact resolve eq2274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq2294 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq19 (M.op x X0) (k X0 X0) X2
       have i₂ := eq2275 X0 x
       grind)
    | exact superpose eq2275 eq19
    | (have j1 := eq2275 X0 x
       grind)
    | exact resolve eq19 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2305 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1412 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1412
    | exact resolve eq1412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq2343 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2305 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2305
    | (have j0 := eq2305 X0 X1
       grind)
    | exact resolve eq2305 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2305
  have eq2344 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2343 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2343
    | (have j0 := eq2343 X0 X1
       grind)
    | exact resolve eq2343 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq2377 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2294 X0 (M.op X0 x)
       have i₂ := eq2344 X0 x
       grind)
    | exact superpose eq2344 eq2294
    | (have j0 := eq2294 X0 x
       have j1 := eq2344 X0 x
       grind)
    | exact resolve eq2294 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294 eq2344
  have eq2405 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2409 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2405 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2405 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2405 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2441 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq2409 X0
       grind)
    | exact superpose eq2409 eq287
    | (have j0 := eq287 X0
       grind)
    | exact resolve eq287 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq2449 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq193 X0 X0
       have i₂ := eq2409 X0
       grind)
    | exact superpose eq2409 eq193
    | (have j0 := eq193 X0 X0
       grind)
    | exact resolve eq193 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2471 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2409 (σ X0)
       grind)
    | exact superpose eq2409 eq15
    | exact resolve eq15 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2479 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq2409 (τ X0)
       grind)
    | exact superpose eq2409 eq43
    | exact resolve eq43 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2501 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq2522 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2479 X0
       have i₂ := eq2409 X0
       grind)
    | exact superpose eq2409 eq2479
    | exact resolve eq2479 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2529 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2471 X0
       have i₂ := eq2409 X0
       grind)
    | exact superpose eq2409 eq2471
    | exact resolve eq2471 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409 eq2471
  have eq2791 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq2529 X0
       grind)
    | exact superpose eq2529 eq34
    | exact resolve eq34 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2796 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (σ X0) (σ X0)
       have i₂ := eq2529 X0
       grind)
    | exact superpose eq2529 eq19
    | exact resolve eq19 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4046 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2441 (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq2441
    | (have j0 := eq2441 (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | exact resolve eq2441 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq4068 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4046 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4046
  have eq4084 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4068 X0 X1
       have i₂ := eq2522 (σ X0)
       grind)
    | exact superpose eq2522 eq4068
    | (have j0 := eq4068 X0 X1
       grind)
    | exact resolve eq4068 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq4102 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4084 X0 X1
       have i₂ := eq2529 X0
       grind)
    | exact superpose eq2529 eq4084
    | (have j0 := eq4084 X0 X1
       grind)
    | exact resolve eq4084 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084
  have eq4117 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4102 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4102
    | (have j0 := eq4102 X0 X1
       grind)
    | exact resolve eq4102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102
  have eq4129 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4117 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4117
    | (have j0 := eq4117 X0 X1
       grind)
    | exact resolve eq4117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq15597 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq4129 X1 X0
       grind)
    | exact superpose eq4129 eq11
    | (have j1 := eq4129 X1 X0
       grind)
    | exact resolve eq11 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq15694 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15597 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15597
    | (have j0 := eq15597 X0 X1
       grind)
    | exact resolve eq15597 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15597
  have eq15826 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq15694 (σ X1) X0
       grind)
    | exact superpose eq15694 eq15
    | (have j1 := eq15694 (σ X1) X0
       grind)
    | exact resolve eq15 eq15694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15694
  have eq32140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15826 x y
       grind)
    | exact superpose eq15826 eq16
    | (have j1 := eq15826 x y
       grind)
    | exact resolve eq16 eq15826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32271 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15826 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15826
  have eq33131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32140
       have i₂ := eq440 y x
       grind)
    | exact superpose eq440 eq32140
    | (have j1 := eq440 x x
       grind)
    | (have r₁ := eq32140
       have r₂ := eq440 y x
       grind)
    | exact resolve eq32140 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq32140
  have eq33132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq33131
  have eq33133 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33132
  have eq33352 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq33133
       grind)
    | exact superpose eq33133 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq33133
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq33133
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq33133
       grind)
    | exact resolve eq13 eq33133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33133
  have eq33379 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33352
  have eq33380 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33379
  have eq33418 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32271 x y
       have i₂ := eq33380
       grind)
    | exact superpose eq33380 eq32271
    | (have j0 := eq32271 x y
       grind)
    | exact resolve eq32271 eq33380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32271 eq33380
  have eq33421 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33418
  have eq33422 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33421
  have eq33702 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2796 y (σ x)
       have i₂ := eq33422
       grind)
    | exact superpose eq33422 eq2796
    | exact resolve eq2796 eq33422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796
  have eq33707 : ∀ X0 : G, x = (M.op x x) ∨ (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ x) (σ y) X0
       have i₂ := eq33422
       grind)
    | exact superpose eq33422 eq19
    | exact resolve eq19 eq33422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33422
  have eq34502 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 x X1
       have i₂ := eq33707 X0
       grind)
    | exact superpose eq33707 eq34
    | (have j1 := eq33707 X1
       grind)
    | (have r₁ := eq34 x X1
       have r₂ := eq33707 X0
       grind)
    | exact resolve eq34 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34508 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2501 x
       have i₂ := eq33707 X0
       grind)
    | exact superpose eq33707 eq2501
    | (have j0 := eq2501 x
       have j1 := eq33707 X0
       grind)
    | exact resolve eq2501 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33707
  have eq34568 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq34508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34508
  have eq34574 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) X1)) ∨ (k X0 x) = (M.op x X0) := by
    intro X0 X1
    first
    | (have j0 := eq34502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34502
  have eq34578 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq34568 X0
       have i₂ := eq2529 x
       grind)
    | exact superpose eq2529 eq34568
    | (have j0 := eq34568 X0
       grind)
    | exact resolve eq34568 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34568
  have eq36604 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq34574 X0 (σ (M.op y y))
       have i₂ := eq33702
       grind)
    | exact superpose eq33702 eq34574
    | (have j0 := eq34574 X0 x
       grind)
    | exact resolve eq34574 eq33702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33702 eq34574
  have eq36685 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq36604 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq36604 X0
       have r₂ := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq36604 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq36604 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36604
  have eq36695 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq36685 X0
       have i₂ := eq2529 y
       grind)
    | exact superpose eq2529 eq36685
    | (have j0 := eq36685 X0
       grind)
    | exact resolve eq36685 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36685
  have eq36757 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq36695 (τ X0)
       grind)
    | exact superpose eq36695 eq17
    | exact resolve eq17 eq36695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq36695
  have eq36989 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq34578 (M.op (σ y) x)
       have i₂ := eq34578 x
       grind)
    | exact superpose eq34578 eq34578
    | exact resolve eq34578 eq34578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34578
  have eq37064 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq36989
  have eq37085 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq37064
       have i₂ := eq2529 y
       grind)
    | exact superpose eq2529 eq37064
    | exact resolve eq37064 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37064
  have eq37121 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq37085
       grind)
    | exact superpose eq37085 eq10
    | exact resolve eq10 eq37085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37085
  have eq37303 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq37121
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq37121
    | exact resolve eq37121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37121
  have eq37531 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2441 y
       have i₂ := eq37303
       grind)
    | exact superpose eq37303 eq2441
    | (have j0 := eq2441 y
       grind)
    | exact resolve eq2441 eq37303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441 eq37303
  have eq37597 : (τ y) = (M.op (τ y) (τ y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq37531
  have eq37605 : (σ x) = (σ (M.op x x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq37597
       have i₂ := eq2522 y
       grind)
    | exact superpose eq2522 eq37597
    | exact resolve eq37597 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522 eq37597
  have eq38346 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (τ y) = (τ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq2791 x x
       have i₂ := eq37605
       grind)
    | exact superpose eq37605 eq2791
    | (have r₁ := eq2791 x x
       have r₂ := eq37605
       grind)
    | exact resolve eq2791 eq37605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37605
  have eq38480 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (τ y) = (τ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq38346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38346
  have eq43426 : ∀ X0 : G, (τ y) = (τ (M.op y y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq38480 (σ X0)
       grind)
    | exact superpose eq38480 eq15
    | exact resolve eq15 eq38480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38480
  have eq54425 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq36757 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36757
    | exact resolve eq36757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36757
  have eq54618 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (σ (k X0 x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq54425 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq54425
    | exact resolve eq54425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54425
  have eq62786 : ∀ X0 : G, (M.op y y) = (σ (τ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq43426 X0
       grind)
    | exact superpose eq43426 eq11
    | (have j1 := eq43426 X0
       grind)
    | exact resolve eq11 eq43426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43426
  have eq63034 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq62786 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq62786
    | (have j0 := eq62786 X0
       grind)
    | exact resolve eq62786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62786
  have eq63533 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2501 y
       have i₂ := eq63034 X0
       grind)
    | exact superpose eq63034 eq2501
    | (have j0 := eq2501 y
       have j1 := eq63034 X0
       grind)
    | exact resolve eq2501 eq63034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63034
  have eq63596 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have j0 := eq63533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63533
  have eq63606 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq63596 X0
       have i₂ := eq2529 y
       grind)
    | exact superpose eq2529 eq63596
    | (have j0 := eq63596 X0
       grind)
    | exact resolve eq63596 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63596
  have eq74287 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63606 y
       grind)
    | exact superpose eq63606 eq16
    | exact resolve eq16 eq63606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63606
  have eq74511 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq74287
       have r₂ := eq54618 y
       grind)
    | exact resolve eq74287 eq54618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54618 eq74287
  have eq74589 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq74511
       grind)
    | exact superpose eq74511 eq10
    | exact resolve eq10 eq74511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74601 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq40 (M.op y y) X0
       have i₂ := eq74511
       grind)
    | exact superpose eq74511 eq40
    | exact resolve eq40 eq74511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74511
  have eq74877 : ∀ X0 : G, (k y (τ X0)) = (k (M.op y y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq74601 X0
       have i₂ := eq40 y X0
       grind)
    | exact superpose eq40 eq74601
    | exact resolve eq74601 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq74601
  have eq74889 : y = (M.op y y) := by
    first
    | (have i₁ := eq74589
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq74589
    | exact resolve eq74589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74589
  have eq83939 : ∀ X0 : G, (k y (τ X0)) = (M.op (τ X0) (M.op y y)) ∨ (M.op y y) = (M.op (τ X0) (M.op y y)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op y y) (τ X0)
       have i₂ := eq74877 X0
       grind)
    | exact superpose eq74877 eq14
    | (have j0 := eq14 (M.op y y) (τ X0)
       grind)
    | exact resolve eq14 eq74877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74877
  have eq84012 : ∀ X0 : G, (k y (τ X0)) = (M.op (τ X0) y) ∨ (M.op y y) = (M.op (τ X0) (M.op y y)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq83939 X0
       have i₂ := eq74889
       grind)
    | exact superpose eq74889 eq83939
    | (have j0 := eq83939 X0
       grind)
    | exact resolve eq83939 eq74889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83939
  have eq84077 : ∀ X0 : G, (k y (τ X0)) = (M.op (τ X0) y) ∨ (M.op y y) = (M.op (τ X0) (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq84012 X0
       have j1 := eq12 y (τ X0)
       grind)
    | (have r₁ := eq84012 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq84012 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84012
  have eq84101 : ∀ X0 : G, y = (M.op (τ X0) y) ∨ (k y (τ X0)) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq84077 X0
       have i₂ := eq74889
       grind)
    | exact superpose eq74889 eq84077
    | (have j0 := eq84077 X0
       grind)
    | exact resolve eq84077 eq74889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74889 eq84077
  have eq127895 : ∀ X0 : G, y ≠ y ∨ y = (k y (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k y (τ X0)) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq13 y (τ X0)
       have i₂ := eq84101 X0
       grind)
    | exact superpose eq84101 eq13
    | (have j0 := eq13 y (τ X0)
       have j1 := eq84101 X0
       grind)
    | (have r₁ := eq13 y (τ X0)
       have r₂ := eq84101 X0
       grind)
    | exact resolve eq13 eq84101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127925 : ∀ X0 : G, y = (k y (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k y (τ X0)) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have j0 := eq127895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127895
  have eq127929 : ∀ X0 : G, y = (k y (τ X0)) ∨ (k y (τ X0)) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have j0 := eq127925 X0
       have j1 := eq12 y (τ X0)
       grind)
    | (have r₁ := eq127925 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq127925 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127925
  have eq137512 : ∀ X0 : G, y ≠ (M.op (τ X0) y) ∨ (k y (τ X0)) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have j0 := eq127929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127929
  have eq137522 : ∀ X0 : G, (k y (τ X0)) = (M.op (τ X0) y) := by
    intro X0
    first
    | (have j0 := eq137512 X0
       have j1 := eq84101 X0
       grind)
    | (have r₁ := eq137512 X0
       have r₂ := eq84101 X0
       grind)
    | exact resolve eq137512 eq84101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84101 eq137512
  have eq138133 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq137522 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137522
    | exact resolve eq137522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137522
  have eq138314 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq138133 x
       grind)
    | exact superpose eq138133 eq180
    | exact resolve eq180 eq138133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq138450 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq138314
  have eq138478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq138450
       have i₂ := eq2529 x
       grind)
    | exact superpose eq2529 eq138450
    | exact resolve eq138450 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138450
  have eq185481 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138478
       grind)
    | exact superpose eq138478 eq16
    | exact resolve eq16 eq138478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185529 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq138478
       grind)
    | exact superpose eq138478 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq138478
       grind)
    | exact resolve eq13 eq138478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138478
  have eq185560 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq185529
  have eq185567 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq2501 x
       grind)
    | (have r₁ := eq185560
       have r₂ := eq2501 x
       grind)
    | exact resolve eq185560 eq2501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq185560
  have eq185583 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq185567
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq185567
    | exact resolve eq185567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185567
  have eq185589 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq185583
       have i₂ := eq138133 x
       grind)
    | exact superpose eq138133 eq185583
    | exact resolve eq185583 eq138133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138133 eq185583
  have eq185592 : (σ x) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq185589
       have i₂ := eq2529 x
       grind)
    | exact superpose eq2529 eq185589
    | exact resolve eq185589 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529 eq185589
  have eq185594 : (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq185592
       have r₂ := eq185481
       grind)
    | exact resolve eq185592 eq185481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185481 eq185592
  have eq187234 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2791 x x
       have i₂ := eq185594
       grind)
    | exact superpose eq185594 eq2791
    | (have r₁ := eq2791 x x
       have r₂ := eq185594
       grind)
    | exact resolve eq2791 eq185594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791
  have eq187256 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq185594
       grind)
    | exact superpose eq185594 eq10
    | exact resolve eq10 eq185594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185594
  have eq187511 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq187234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187234
  have eq187669 : x = (M.op x x) := by
    first
    | (have i₁ := eq187256
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq187256
    | exact resolve eq187256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187256
  have eq187719 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq34 x x
       have i₂ := eq187669
       grind)
    | exact superpose eq187669 eq34
    | (have r₁ := eq34 x x
       have r₂ := eq187669
       grind)
    | exact resolve eq34 eq187669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq187669
  have eq187812 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq187719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187719
  have eq191272 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq187511 (σ X0)
       grind)
    | exact superpose eq187511 eq15
    | exact resolve eq15 eq187511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187511
  have eq191553 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq191272 X0
       have i₂ := eq187812 X0
       grind)
    | exact superpose eq187812 eq191272
    | exact resolve eq191272 eq187812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187812 eq191272
  have eq201079 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq191553 y
       grind)
    | exact superpose eq191553 eq16
    | (have r₁ := eq16
       have r₂ := eq191553 y
       grind)
    | exact resolve eq16 eq191553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191553
  have eq201287 : False := by grind
  exact eq201287

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq275 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq277 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | (have j0 := eq275 X0
       grind)
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq280 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq286 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq280 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq280
    | (have j0 := eq280 (τ X0)
       grind)
    | exact resolve eq280 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq2846 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq78 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2847 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2846 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq2852 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2847 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2847
    | (have j0 := eq2847 X0
       grind)
    | exact resolve eq2847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq2854 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2852 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2852
    | exact resolve eq2852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq2892 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2854 X0
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq2854
    | (have j0 := eq2854 X0
       grind)
    | exact resolve eq2854 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq2897 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2892 X0
       grind)
    | exact superpose eq2892 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2892 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2892 X0
       grind)
    | exact resolve eq12 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq2920 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2897 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897
  have eq3130 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2920 X0 X1
       grind)
    | exact superpose eq2920 eq11
    | (have j1 := eq2920 X0 X1
       grind)
    | exact resolve eq11 eq2920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920
  have eq3207 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3130 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3130
    | (have j0 := eq3130 X0 X0
       grind)
    | exact resolve eq3130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3330 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3207 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq3331 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3330 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330
  have eq3447 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq3331 X0
       grind)
    | exact superpose eq3331 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq3448 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq3331 X0
       grind)
    | exact superpose eq3331 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq3451 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq3331 X0
       grind)
    | exact superpose eq3331 eq286
    | (have j0 := eq286 X0
       grind)
    | exact resolve eq286 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq3481 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3331 (σ X0)
       grind)
    | exact superpose eq3331 eq15
    | exact resolve eq15 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3488 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq3331 (τ X0)
       grind)
    | exact superpose eq3331 eq43
    | exact resolve eq43 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3536 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3488 X0
       have i₂ := eq3331 X0
       grind)
    | exact superpose eq3331 eq3488
    | exact resolve eq3488 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3543 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3481 X0
       have i₂ := eq3331 X0
       grind)
    | exact superpose eq3331 eq3481
    | exact resolve eq3481 eq3331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331 eq3481
  have eq3830 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq3543 X0
       grind)
    | exact superpose eq3543 eq34
    | exact resolve eq34 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5355 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3451 (σ X0)
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq3451
    | (have j0 := eq3451 (σ X0)
       have j1 := eq82 X1 X0
       grind)
    | exact resolve eq3451 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq3451
  have eq5372 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5355 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5355
  have eq5388 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5372 X0 X1
       have i₂ := eq3536 (σ X0)
       grind)
    | exact superpose eq3536 eq5372
    | (have j0 := eq5372 X0 X1
       grind)
    | exact resolve eq5372 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536 eq5372
  have eq5406 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5388 X0 X1
       have i₂ := eq3543 X0
       grind)
    | exact superpose eq3543 eq5388
    | (have j0 := eq5388 X0 X1
       grind)
    | exact resolve eq5388 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5388
  have eq5419 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5406 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5406
    | (have j0 := eq5406 X0 X1
       grind)
    | exact resolve eq5406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406
  have eq5428 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5419 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5419
    | (have j0 := eq5419 X0 X1
       grind)
    | exact resolve eq5419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419
  have eq26086 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq5428 X1 X0
       grind)
    | exact superpose eq5428 eq11
    | (have j1 := eq5428 X1 X0
       grind)
    | exact resolve eq11 eq5428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq26207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26086 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq26086
    | (have j0 := eq26086 X0 X1
       grind)
    | exact resolve eq26086 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq26086
  have eq26364 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq26207 (σ X0) X1
       grind)
    | exact superpose eq26207 eq15
    | (have j1 := eq26207 (σ X0) X1
       grind)
    | exact resolve eq15 eq26207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26207
  have eq44068 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26364 x y
       grind)
    | exact superpose eq26364 eq16
    | (have j1 := eq26364 x y
       grind)
    | exact resolve eq16 eq26364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26364
  have eq44691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44068
       have i₂ := eq437 x y
       grind)
    | exact superpose eq437 eq44068
    | (have j1 := eq437 y y
       grind)
    | (have r₁ := eq44068
       have r₂ := eq437 x y
       grind)
    | exact resolve eq44068 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq44068
  have eq44692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq44691
  have eq44693 : y = (M.op y x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq44692
  have eq44700 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 y x
       have i₂ := eq44693
       grind)
    | exact superpose eq44693 eq19
    | exact resolve eq19 eq44693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44693
  have eq44996 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq44700 (M.op x y)
       have i₂ := eq44700 x
       grind)
    | exact superpose eq44700 eq44700
    | exact resolve eq44700 eq44700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44700
  have eq45045 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq44996
  have eq45074 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ y) (σ x)
       have i₂ := eq45045
       grind)
    | exact superpose eq45045 eq19
    | exact resolve eq19 eq45045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq45045
  have eq46082 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45074 (M.op x (σ y))
       have i₂ := eq45074 x
       grind)
    | exact superpose eq45074 eq45074
    | exact resolve eq45074 eq45074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45074
  have eq46149 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq46082
  have eq46161 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq46149
       have i₂ := eq3543 y
       grind)
    | exact superpose eq3543 eq46149
    | exact resolve eq46149 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46149
  have eq46177 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3447 y
       have i₂ := eq46161
       grind)
    | exact superpose eq46161 eq3447
    | (have j0 := eq3447 y
       grind)
    | (have r₁ := eq3447 y
       have r₂ := eq46161
       grind)
    | exact resolve eq3447 eq46161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46192 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq3830 y x
       have i₂ := eq46161
       grind)
    | exact superpose eq46161 eq3830
    | (have r₁ := eq3830 y x
       have r₂ := eq46161
       grind)
    | exact resolve eq3830 eq46161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3830 eq46161
  have eq46252 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq46192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46192
  have eq46259 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq46177
  have eq46268 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq46252 X0
       have j1 := eq3448 y X0
       grind)
    | (have r₁ := eq46252 X0
       have r₂ := eq3448 y x
       grind)
    | exact resolve eq46252 eq3448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448 eq46252
  have eq46274 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq3447 y
       grind)
    | (have r₁ := eq46259
       have r₂ := eq3447 y
       grind)
    | exact resolve eq46259 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447 eq46259
  have eq46282 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq46274
       have i₂ := eq3543 y
       grind)
    | exact superpose eq3543 eq46274
    | exact resolve eq46274 eq3543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543 eq46274
  have eq46805 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq46282
       grind)
    | exact superpose eq46282 eq10
    | exact resolve eq10 eq46282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46282
  have eq47022 : y = (M.op y y) := by
    first
    | (have i₁ := eq46805
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq46805
    | exact resolve eq46805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46805
  have eq47070 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq34 y x
       have i₂ := eq47022
       grind)
    | exact superpose eq47022 eq34
    | (have r₁ := eq34 y x
       have r₂ := eq47022
       grind)
    | exact resolve eq34 eq47022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq47022
  have eq47166 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq47070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47070
  have eq48048 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq46268 (σ X0)
       grind)
    | exact superpose eq46268 eq15
    | exact resolve eq15 eq46268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46268
  have eq48159 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq48048 X0
       have i₂ := eq47166 X0
       grind)
    | exact superpose eq47166 eq48048
    | exact resolve eq48048 eq47166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47166 eq48048
  have eq50367 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48159 x
       grind)
    | exact superpose eq48159 eq16
    | (have r₁ := eq16
       have r₂ := eq48159 x
       grind)
    | exact resolve eq16 eq48159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48159
  have eq50502 : False := by grind
  exact eq50502

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq275 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq277 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | (have j0 := eq275 X0
       grind)
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq280 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq286 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq280 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq280
    | (have j0 := eq280 (τ X0)
       grind)
    | exact resolve eq280 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq2851 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq78 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2852 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851
  have eq2857 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2852 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2852
    | (have j0 := eq2852 X0
       grind)
    | exact resolve eq2852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq2860 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2857 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2857
    | exact resolve eq2857 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2898 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2860 X0
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq2860
    | (have j0 := eq2860 X0
       grind)
    | exact resolve eq2860 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2903 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2898 X0
       grind)
    | exact superpose eq2898 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2898 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2898 X0
       grind)
    | exact resolve eq12 eq2898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898
  have eq2926 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2903 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2903
  have eq3136 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2926 X0 X1
       grind)
    | exact superpose eq2926 eq11
    | (have j1 := eq2926 X0 X1
       grind)
    | exact resolve eq11 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq3213 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3136 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3136
    | (have j0 := eq3136 X0 X0
       grind)
    | exact resolve eq3136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136
  have eq3336 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3213 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq3337 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3453 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq3337 X0
       grind)
    | exact superpose eq3337 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq3454 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq3337 X0
       grind)
    | exact superpose eq3337 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq3457 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq3337 X0
       grind)
    | exact superpose eq3337 eq286
    | (have j0 := eq286 X0
       grind)
    | exact resolve eq286 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq3487 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3337 (σ X0)
       grind)
    | exact superpose eq3337 eq15
    | exact resolve eq15 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3494 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq3337 (τ X0)
       grind)
    | exact superpose eq3337 eq43
    | exact resolve eq43 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3542 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3494 X0
       have i₂ := eq3337 X0
       grind)
    | exact superpose eq3337 eq3494
    | exact resolve eq3494 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq3549 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3487 X0
       have i₂ := eq3337 X0
       grind)
    | exact superpose eq3337 eq3487
    | exact resolve eq3487 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337 eq3487
  have eq3838 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq3549 X0
       grind)
    | exact superpose eq3549 eq34
    | exact resolve eq34 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5370 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3457 (σ X0)
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq3457
    | (have j0 := eq3457 (σ X0)
       have j1 := eq82 X1 X0
       grind)
    | exact resolve eq3457 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq3457
  have eq5387 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370
  have eq5403 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5387 X0 X1
       have i₂ := eq3542 (σ X0)
       grind)
    | exact superpose eq3542 eq5387
    | (have j0 := eq5387 X0 X1
       grind)
    | exact resolve eq5387 eq3542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542 eq5387
  have eq5421 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5403 X0 X1
       have i₂ := eq3549 X0
       grind)
    | exact superpose eq3549 eq5403
    | (have j0 := eq5403 X0 X1
       grind)
    | exact resolve eq5403 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq5434 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5421 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5421
    | (have j0 := eq5421 X0 X1
       grind)
    | exact resolve eq5421 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5421
  have eq5443 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5434 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5434
    | (have j0 := eq5434 X0 X1
       grind)
    | exact resolve eq5434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434
  have eq26623 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq5443 X1 X0
       grind)
    | exact superpose eq5443 eq11
    | (have j1 := eq5443 X1 X0
       grind)
    | exact resolve eq11 eq5443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5443
  have eq26736 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26623 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq26623
    | (have j0 := eq26623 X0 X1
       grind)
    | exact resolve eq26623 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq26623
  have eq26890 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq26736 (σ X0) X1
       grind)
    | exact superpose eq26736 eq15
    | (have j1 := eq26736 (σ X0) X1
       grind)
    | exact resolve eq15 eq26736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26736
  have eq45753 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26890 x y
       grind)
    | exact superpose eq26890 eq16
    | (have j1 := eq26890 x y
       grind)
    | exact resolve eq16 eq26890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26890
  have eq46601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45753
       have i₂ := eq437 x y
       grind)
    | exact superpose eq437 eq45753
    | (have j1 := eq437 y y
       grind)
    | (have r₁ := eq45753
       have r₂ := eq437 x y
       grind)
    | exact resolve eq45753 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq45753
  have eq46602 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq46601
  have eq46603 : y = (M.op y x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq46602
  have eq46610 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 y x
       have i₂ := eq46603
       grind)
    | exact superpose eq46603 eq19
    | exact resolve eq19 eq46603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46603
  have eq47135 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq46610 (M.op x y)
       have i₂ := eq46610 x
       grind)
    | exact superpose eq46610 eq46610
    | exact resolve eq46610 eq46610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46610
  have eq47183 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq47135
  have eq47212 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ y) (σ x)
       have i₂ := eq47183
       grind)
    | exact superpose eq47183 eq19
    | exact resolve eq19 eq47183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47183
  have eq47994 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq47212 (M.op x (σ y))
       have i₂ := eq47212 x
       grind)
    | exact superpose eq47212 eq47212
    | exact resolve eq47212 eq47212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47212
  have eq48060 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq47994
  have eq48070 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq48060
       have i₂ := eq3549 y
       grind)
    | exact superpose eq3549 eq48060
    | exact resolve eq48060 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48060
  have eq48087 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3453 y
       have i₂ := eq48070
       grind)
    | exact superpose eq48070 eq3453
    | (have j0 := eq3453 y
       grind)
    | (have r₁ := eq3453 y
       have r₂ := eq48070
       grind)
    | exact resolve eq3453 eq48070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48102 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq3838 y x
       have i₂ := eq48070
       grind)
    | exact superpose eq48070 eq3838
    | (have r₁ := eq3838 y x
       have r₂ := eq48070
       grind)
    | exact resolve eq3838 eq48070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838 eq48070
  have eq48161 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq48102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48102
  have eq48168 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq48087
  have eq48177 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq48161 X0
       have j1 := eq3454 y X0
       grind)
    | (have r₁ := eq48161 X0
       have r₂ := eq3454 y x
       grind)
    | exact resolve eq48161 eq3454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454 eq48161
  have eq48183 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq3453 y
       grind)
    | (have r₁ := eq48168
       have r₂ := eq3453 y
       grind)
    | exact resolve eq48168 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453 eq48168
  have eq48191 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq48183
       have i₂ := eq3549 y
       grind)
    | exact superpose eq3549 eq48183
    | exact resolve eq48183 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549 eq48183
  have eq48708 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq48191
       grind)
    | exact superpose eq48191 eq10
    | exact resolve eq10 eq48191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48191
  have eq48934 : y = (M.op y y) := by
    first
    | (have i₁ := eq48708
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq48708
    | exact resolve eq48708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48708
  have eq48987 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq34 y x
       have i₂ := eq48934
       grind)
    | exact superpose eq48934 eq34
    | (have r₁ := eq34 y x
       have r₂ := eq48934
       grind)
    | exact resolve eq34 eq48934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq48934
  have eq49082 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq48987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48987
  have eq50762 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq48177 (σ X0)
       grind)
    | exact superpose eq48177 eq15
    | exact resolve eq15 eq48177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48177
  have eq50877 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq50762 X0
       have i₂ := eq49082 X0
       grind)
    | exact superpose eq49082 eq50762
    | exact resolve eq50762 eq49082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49082 eq50762
  have eq53357 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50877 x
       grind)
    | exact superpose eq50877 eq16
    | (have r₁ := eq16
       have r₂ := eq50877 x
       grind)
    | exact resolve eq16 eq50877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50877
  have eq53493 : False := by grind
  exact eq53493

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1060 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq431 X0 (σ X1)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X0 (σ X1)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1111 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1060 X0 (τ X1)
       grind)
    | exact superpose eq1060 eq17
    | (have j1 := eq1060 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1060
  have eq1316 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1111
    | exact resolve eq1111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1316
    | (have j0 := eq1316 X0 X1
       grind)
    | exact resolve eq1316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1886 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1071 x y
       grind)
    | exact superpose eq1071 eq16
    | (have j1 := eq1071 x y
       grind)
    | exact resolve eq16 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq2096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1886
       have i₂ := eq1388 y x
       grind)
    | exact superpose eq1388 eq1886
    | (have j1 := eq1388 (σ y) (σ x)
       grind)
    | (have r₁ := eq1886
       have r₂ := eq1388 y x
       grind)
    | exact resolve eq1886 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2097 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2096
  have eq2104 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq62
    | exact resolve eq62 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2192 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2104 y
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq2104
    | exact resolve eq2104 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq2104
  have eq2207 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2192
  have eq2211 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq16
    | exact resolve eq16 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2217 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq61
    | exact resolve eq61 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2207
  have eq2309 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2217 (M.op x (σ x))
       have i₂ := eq2217 x
       grind)
    | exact superpose eq2217 eq2217
    | exact resolve eq2217 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2333 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2309
  have eq2336 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2333
       have i₂ := eq376 x
       grind)
    | exact superpose eq376 eq2333
    | exact resolve eq2333 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2333
  have eq2347 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq430 x X0
       have i₂ := eq2336
       grind)
    | exact superpose eq2336 eq430
    | (have j0 := eq430 x X0
       grind)
    | (have r₁ := eq430 x x
       have r₂ := eq2336
       grind)
    | exact resolve eq430 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2375 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347
  have eq2378 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2375 X0
       have j1 := eq430 x X0
       grind)
    | (have r₁ := eq2375 X0
       have r₂ := eq430 x x
       grind)
    | exact resolve eq2375 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2375
  have eq2391 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2378 (σ X0)
       grind)
    | exact superpose eq2378 eq15
    | exact resolve eq15 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2508 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2391 y
       grind)
    | exact superpose eq2391 eq16
    | exact resolve eq16 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2609 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2508
       have i₂ := eq1388 y x
       grind)
    | exact superpose eq1388 eq2508
    | (have j1 := eq1388 y x
       grind)
    | (have r₁ := eq2508
       have r₂ := eq1388 y x
       grind)
    | exact resolve eq2508 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq2610 : x = (M.op x y) := by grind
  clear eq2609
  have eq2613 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2211
       have i₂ := eq2610
       grind)
    | exact superpose eq2610 eq2211
    | exact resolve eq2211 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211 eq2610
  have eq2631 : x = (M.op x x) := by grind
  clear eq2613
  have eq2635 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq92 x x
       have i₂ := eq2631
       grind)
    | exact superpose eq2631 eq92
    | (have r₁ := eq92 x x
       have r₂ := eq2631
       grind)
    | exact resolve eq92 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2631
  have eq2670 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2770 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2508
       have i₂ := eq2670 y
       grind)
    | exact superpose eq2670 eq2508
    | exact resolve eq2508 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508 eq2670
  have eq2773 : False := by grind
  exact eq2773

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1060 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq431 X0 (σ X1)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X0 (σ X1)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1111 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1060 X0 (τ X1)
       grind)
    | exact superpose eq1060 eq17
    | (have j1 := eq1060 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1060
  have eq1316 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1111
    | exact resolve eq1111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1316
    | (have j0 := eq1316 X0 X1
       grind)
    | exact resolve eq1316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1886 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1071 x y
       grind)
    | exact superpose eq1071 eq16
    | (have j1 := eq1071 x y
       grind)
    | exact resolve eq16 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq2096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1886
       have i₂ := eq1388 y x
       grind)
    | exact superpose eq1388 eq1886
    | (have j1 := eq1388 (σ y) (σ x)
       grind)
    | (have r₁ := eq1886
       have r₂ := eq1388 y x
       grind)
    | exact resolve eq1886 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2097 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2096
  have eq2104 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq62
    | exact resolve eq62 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2193 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2104 y
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq2104
    | exact resolve eq2104 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq2104
  have eq2208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2193
  have eq2212 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2208
       grind)
    | exact superpose eq2208 eq16
    | exact resolve eq16 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2218 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2208
       grind)
    | exact superpose eq2208 eq61
    | exact resolve eq61 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2208
  have eq2312 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2218 (M.op x (σ x))
       have i₂ := eq2218 x
       grind)
    | exact superpose eq2218 eq2218
    | exact resolve eq2218 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq2336 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2312
  have eq2339 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2336
       have i₂ := eq376 x
       grind)
    | exact superpose eq376 eq2336
    | exact resolve eq2336 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2336
  have eq2350 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq430 x X0
       have i₂ := eq2339
       grind)
    | exact superpose eq2339 eq430
    | (have j0 := eq430 x X0
       grind)
    | (have r₁ := eq430 x x
       have r₂ := eq2339
       grind)
    | exact resolve eq430 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2378 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2381 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2378 X0
       have j1 := eq430 x X0
       grind)
    | (have r₁ := eq2378 X0
       have r₂ := eq430 x x
       grind)
    | exact resolve eq2378 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2378
  have eq2394 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2381 (σ X0)
       grind)
    | exact superpose eq2381 eq15
    | exact resolve eq15 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381
  have eq2511 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2394 y
       grind)
    | exact superpose eq2394 eq16
    | exact resolve eq16 eq2394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2613 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2511
       have i₂ := eq1388 y x
       grind)
    | exact superpose eq1388 eq2511
    | (have j1 := eq1388 y x
       grind)
    | (have r₁ := eq2511
       have r₂ := eq1388 y x
       grind)
    | exact resolve eq2511 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq2614 : x = (M.op x y) := by grind
  clear eq2613
  have eq2617 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2212
       have i₂ := eq2614
       grind)
    | exact superpose eq2614 eq2212
    | exact resolve eq2212 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212 eq2614
  have eq2635 : x = (M.op x x) := by grind
  clear eq2617
  have eq2639 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq92 x x
       have i₂ := eq2635
       grind)
    | exact superpose eq2635 eq92
    | (have r₁ := eq92 x x
       have r₂ := eq2635
       grind)
    | exact resolve eq92 eq2635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2635
  have eq2674 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2774 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2511
       have i₂ := eq2674 y
       grind)
    | exact superpose eq2674 eq2511
    | exact resolve eq2511 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511 eq2674
  have eq2777 : False := by grind
  exact eq2777

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq184 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1198 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1199 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1405 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1406 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq2150 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1199 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1199
    | exact resolve eq1199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq2188 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2150 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2150
    | (have j0 := eq2150 X0 X1
       grind)
    | exact resolve eq2150 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2189 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2188 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2188
    | (have j0 := eq2188 X0 X1
       grind)
    | exact resolve eq2188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2264 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq19 (M.op x X0) (k X0 X0) X2
       have i₂ := eq2189 X0 x
       grind)
    | exact superpose eq2189 eq19
    | (have j1 := eq2189 X0 x
       grind)
    | exact resolve eq19 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq2311 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1406 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1406
    | exact resolve eq1406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq2349 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2311 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2311
    | (have j0 := eq2311 X0 X1
       grind)
    | exact resolve eq2311 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2311
  have eq2350 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2349 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2349
    | (have j0 := eq2349 X0 X1
       grind)
    | exact resolve eq2349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2364 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2264 X0 (M.op X0 x)
       have i₂ := eq2350 X0 x
       grind)
    | exact superpose eq2350 eq2264
    | (have j0 := eq2264 X0 x
       have j1 := eq2350 X0 x
       grind)
    | exact resolve eq2264 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq2350
  have eq2380 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364
  have eq2384 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2380 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2380 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2380 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2422 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2384 (σ X0)
       grind)
    | exact superpose eq2384 eq15
    | exact resolve eq15 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2479 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2422 X0
       have i₂ := eq2384 X0
       grind)
    | exact superpose eq2384 eq2422
    | exact resolve eq2422 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384 eq2422
  have eq2615 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 (σ X2)) = X0 ∨ (k X2 (τ X0)) = (τ (M.op X0 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq78 X0 X2
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq78 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq78 (σ X1) X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2639 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = (τ (M.op X0 (σ X2))) ∨ (M.op X0 (σ X2)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2615 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq2736 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq2479 X0
       grind)
    | exact superpose eq2479 eq34
    | exact resolve eq34 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93468 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2639 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2639
    | (have j0 := eq2639 X1 X2 X2
       grind)
    | exact resolve eq2639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq93849 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93468 X0 X1 X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq93468
    | (have j0 := eq93468 X0 X1 X2
       grind)
    | exact resolve eq93468 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq93468
  have eq95920 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq93849 X1 X0 X2
       grind)
    | exact superpose eq93849 eq11
    | (have j1 := eq93849 X1 X0 X2
       grind)
    | exact resolve eq11 eq93849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93849
  have eq96157 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95920 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq95920
    | (have j0 := eq95920 X0 X1 X1
       grind)
    | exact resolve eq95920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95920
  have eq97034 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq96157 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96157
  have eq97035 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq97034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97034
  have eq97448 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq97035 (σ X1) (σ X0)
       grind)
    | exact superpose eq97035 eq15
    | (have j1 := eq97035 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq97035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97477 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq97035 (τ X1) X0
       grind)
    | exact superpose eq97035 eq17
    | (have j1 := eq97035 (τ X1) X0
       grind)
    | exact resolve eq17 eq97035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq97035
  have eq99340 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97477 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97477
    | exact resolve eq97477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97477
  have eq99746 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99340 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq99340
    | (have j0 := eq99340 X0 X1
       grind)
    | exact resolve eq99340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99340
  have eq102272 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97448 x y
       grind)
    | exact superpose eq97448 eq16
    | (have j1 := eq97448 x y
       grind)
    | exact resolve eq16 eq97448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97448
  have eq105792 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102272
       have i₂ := eq99746 y x
       grind)
    | exact superpose eq99746 eq102272
    | (have j1 := eq99746 (σ y) (σ x)
       grind)
    | (have r₁ := eq102272
       have r₂ := eq99746 y x
       grind)
    | exact resolve eq102272 eq99746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99746 eq102272
  have eq105795 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq105792
  have eq105803 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x y
       have i₂ := eq105795
       grind)
    | exact superpose eq105795 eq19
    | exact resolve eq19 eq105795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105795
  have eq106329 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105803 (M.op x x)
       have i₂ := eq105803 x
       grind)
    | exact superpose eq105803 eq105803
    | exact resolve eq105803 eq105803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105803
  have eq106423 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq106329
  have eq106469 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ x) (σ y)
       have i₂ := eq106423
       grind)
    | exact superpose eq106423 eq19
    | exact resolve eq19 eq106423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq106423
  have eq112473 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106469 (M.op x (σ x))
       have i₂ := eq106469 x
       grind)
    | exact superpose eq106469 eq106469
    | exact resolve eq106469 eq106469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106469
  have eq112623 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq112473
  have eq112646 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112623
       have i₂ := eq2479 x
       grind)
    | exact superpose eq2479 eq112623
    | exact resolve eq112623 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479 eq112623
  have eq112685 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq112646
       grind)
    | exact superpose eq112646 eq10
    | exact resolve eq10 eq112646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112646
  have eq112982 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112685
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq112685
    | exact resolve eq112685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112685
  have eq112983 : x = (M.op x x) := by grind
  clear eq112982
  have eq114009 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq34 x x
       have i₂ := eq112983
       grind)
    | exact superpose eq112983 eq34
    | (have r₁ := eq34 x x
       have r₂ := eq112983
       grind)
    | exact resolve eq34 eq112983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq114022 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2736 x x
       have i₂ := eq112983
       grind)
    | exact superpose eq112983 eq2736
    | exact resolve eq2736 eq112983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736 eq112983
  have eq114124 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq114022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114022
  have eq114132 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq114009 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114009
  have eq118055 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq114124 (σ X0)
       grind)
    | exact superpose eq114124 eq15
    | exact resolve eq15 eq114124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114124
  have eq118233 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq118055 X0
       have i₂ := eq114132 X0
       grind)
    | exact superpose eq114132 eq118055
    | exact resolve eq118055 eq114132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114132 eq118055
  have eq124696 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118233 y
       grind)
    | exact superpose eq118233 eq16
    | (have r₁ := eq16
       have r₂ := eq118233 y
       grind)
    | exact resolve eq16 eq118233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118233
  have eq124999 : False := by grind
  exact eq124999

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq32 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 X0 X0
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq33
    | exact resolve eq33 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq55 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq56 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq57 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | (have j0 := eq56 X0
       grind)
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq58 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | (have j0 := eq55 X0
       grind)
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq41
    | exact resolve eq41 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq83 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq90 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq185 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq53
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (σ X0) (σ X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq20
    | (have j1 := eq53 X0
       grind)
    | exact resolve eq20 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) (σ X0) X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq20
    | (have j1 := eq53 X0
       grind)
    | exact resolve eq20 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq53 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X2) X3) (k X0 (τ X1)))) = (k (k X2 (σ X3)) (k (σ X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq32
    | exact resolve eq32 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq225 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq39
    | exact resolve eq39 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq301 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq197
    | (have j0 := eq197 (τ X0)
       grind)
    | exact resolve eq197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq301
    | (have j0 := eq301 X0
       grind)
    | exact resolve eq301 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq305 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | (have j0 := eq302 X0
       grind)
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq314 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq305 (τ X0)
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq305
    | (have j0 := eq305 (τ X0)
       grind)
    | exact resolve eq305 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq422 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq399 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq399
    | (have j0 := eq399 X0
       grind)
    | exact resolve eq399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq513 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq546 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq513
    | (have j0 := eq513 (M.op X1 X1) X1
       grind)
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq627 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq188 X0 (σ X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq188
    | (have j0 := eq188 X0 x
       have j1 := eq53 X0
       grind)
    | exact resolve eq188 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq637 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq188 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq188
    | (have j0 := eq188 (τ X0) X1
       grind)
    | exact resolve eq188 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq652 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq655 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq627 X0
       have j1 := eq197 X0
       grind)
    | (have r₁ := eq627 X0
       have r₂ := eq197 X0
       grind)
    | exact resolve eq627 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq659 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq682 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq20 (M.op x X0) (k X0 X0) X2
       have i₂ := eq659 X0 x
       grind)
    | exact superpose eq659 eq20
    | (have j1 := eq659 X0 x
       grind)
    | exact resolve eq20 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq659
  have eq725 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq189 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq748 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq725
    | (have j0 := eq725 X0 X1
       grind)
    | exact resolve eq725 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq752 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq748
    | (have j0 := eq748 X0 X1
       grind)
    | exact resolve eq748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq805 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq752 X0 (M.op (k X0 X0) x)
       have i₂ := eq682 X0 x
       grind)
    | exact superpose eq682 eq752
    | (have j0 := eq752 X0 x
       have j1 := eq682 X0 x
       grind)
    | exact resolve eq752 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq752
  have eq812 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq931 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X2 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq546 X2 X0
       grind)
    | exact superpose eq546 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq546 (M.op X1 X0) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq546 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq546 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq546 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq546 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq954 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq955 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ X0 = X2 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq931 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq960 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq960 X0
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq960
    | (have j0 := eq960 X0
       grind)
    | exact resolve eq960 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1021 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (k (τ X0) X1) (k (τ X0) X1)) ∨ (τ (k (k X0 (σ X1)) (k X0 (σ X1)))) = (M.op (k (τ X0) X1) (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (k X0 (σ X1))
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq83
    | exact resolve eq83 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1045 : ∀ X0 X1 : G, (k (τ (k X0 (σ X1))) (k (τ X0) X1)) = (M.op (k (τ X0) X1) (k (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (k (τ X0) X1) (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1021 X0 X1
       have i₂ := eq45 X0 X1 (k X0 (σ X1))
       grind)
    | exact superpose eq45 eq1021
    | (have j0 := eq1021 X0 X1
       grind)
    | exact resolve eq1021 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1021
  have eq1048 : ∀ X0 X1 : G, (k (k (τ X0) X1) (k (τ X0) X1)) = (M.op (k (τ X0) X1) (k (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (k (τ X0) X1) (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1045 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq1045
    | (have j0 := eq1045 X0 X1
       grind)
    | exact resolve eq1045 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1051 : ∀ X0 X1 : G, (k (k (τ X0) X1) (k (τ X0) X1)) = (M.op (k (τ X0) X1) (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1048 X0 X1
       have j1 := eq12 (k (τ X0) X1) (k (τ X0) X1)
       grind)
    | (have r₁ := eq1048 X0 X1
       have r₂ := eq12 X0 (k (τ X0) X1)
       grind)
    | exact resolve eq1048 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1468 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op (M.op X0 X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq954 X0
       grind)
    | exact superpose eq954 eq10
    | (have j1 := eq954 X0
       grind)
    | exact resolve eq10 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1512 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1468 X0
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq1468
    | (have j0 := eq1468 X0
       grind)
    | exact resolve eq1468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1514 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1512 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq1512 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1512 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1617 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1514 (k (σ X0) X1)
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq1514
    | (have j1 := eq185 X0 X1
       grind)
    | exact resolve eq1514 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq1514
  have eq1629 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1617 X0 X1
       have i₂ := eq225 X0 X1 X0 X1
       grind)
    | exact superpose eq225 eq1617
    | (have j0 := eq1617 X0 X1
       grind)
    | exact resolve eq1617 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq1617
  have eq1630 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1629 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq6839 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (k X0 X0)
       have i₂ := eq655 X0
       grind)
    | exact superpose eq655 eq57
    | (have j0 := eq57 X0
       have j1 := eq655 X0
       grind)
    | exact resolve eq57 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq6899 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq6839 X0
       have j1 := eq197 X0
       grind)
    | (have r₁ := eq6839 X0
       have r₂ := eq197 X0
       grind)
    | exact resolve eq6839 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6839
  have eq6937 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6899 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6899
    | (have j0 := eq6899 X0
       grind)
    | exact resolve eq6899 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6899
  have eq6996 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq211 (τ X0) X0 X0 (τ X0)
       have i₂ := eq6937 (τ X0)
       grind)
    | exact superpose eq6937 eq211
    | (have j1 := eq6937 (τ X0)
       grind)
    | exact resolve eq211 eq6937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6937
  have eq7064 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6996 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6996
    | (have j0 := eq6996 X0
       grind)
    | exact resolve eq6996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7074 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7064 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7064
    | (have j0 := eq7064 X0
       grind)
    | exact resolve eq7064 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7064
  have eq7092 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq211 (τ X0) X0 X0 (τ X0)
       have i₂ := eq7074 (τ X0)
       grind)
    | exact superpose eq7074 eq211
    | (have j1 := eq7074 (τ X0)
       grind)
    | exact resolve eq211 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq7099 : ∀ X0 : G, (τ (σ X0)) = (k (k (τ (σ X0)) X0) (τ (k (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq61 (σ X0) X0 (k (σ X0) (σ X0))
       have i₂ := eq7074 (σ X0)
       grind)
    | exact superpose eq7074 eq61
    | (have j1 := eq7074 (σ X0)
       grind)
    | exact resolve eq61 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq7074
  have eq7169 : ∀ X0 : G, (τ (σ X0)) = (k (k (τ (σ X0)) X0) (k (τ (σ X0)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7099 X0
       have i₂ := eq33 (σ X0) X0
       grind)
    | exact superpose eq33 eq7099
    | (have j0 := eq7099 X0
       grind)
    | exact resolve eq7099 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq7099
  have eq7171 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq7092 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7092
    | (have j0 := eq7092 X0
       grind)
    | exact resolve eq7092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7092
  have eq7179 : ∀ X0 : G, (τ (σ X0)) = (M.op (k (τ (σ X0)) X0) (k (τ (σ X0)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7169 X0
       have i₂ := eq1051 (σ X0) X0
       grind)
    | exact superpose eq1051 eq7169
    | (have j0 := eq7169 X0
       grind)
    | exact resolve eq7169 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq7169
  have eq7183 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7179 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7179
    | (have j0 := eq7179 X0
       grind)
    | exact resolve eq7179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7179
  have eq8464 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (k (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7171 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7171
    | (have j0 := eq7171 (σ X0)
       grind)
    | exact resolve eq7171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7171
  have eq8514 : ∀ X0 : G, (σ X0) = (M.op (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8464 X0
       have i₂ := eq1630 X0 (σ X0)
       grind)
    | exact superpose eq1630 eq8464
    | (have j0 := eq8464 X0
       grind)
    | exact resolve eq8464 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq8464
  have eq8517 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8514 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq8514
    | (have j0 := eq8514 X0
       grind)
    | exact resolve eq8514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8514
  have eq8669 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7183 (τ X0)
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq7183
    | (have j0 := eq7183 (τ X0)
       grind)
    | exact resolve eq7183 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq7183
  have eq8719 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8669 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8669
    | (have j0 := eq8669 X0
       grind)
    | exact resolve eq8669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8669
  have eq8782 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8517 X0
       have i₂ := eq422 X0
       grind)
    | exact superpose eq422 eq8517
    | (have j0 := eq8517 X0
       have j1 := eq422 X0
       grind)
    | exact resolve eq8517 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq8517
  have eq8869 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8782 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8782
  have eq9745 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8719 X0
       have i₂ := eq975 X0
       grind)
    | exact superpose eq975 eq8719
    | (have j0 := eq8719 X0
       have j1 := eq975 X0
       grind)
    | exact resolve eq8719 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq8719
  have eq9821 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9745 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9745
  have eq10749 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8869 (k X0 X0)
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq8869
    | (have j0 := eq8869 X0
       have j1 := eq812 X0
       grind)
    | exact resolve eq8869 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq8869
  have eq10862 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10749 X0
       have j1 := eq305 X0
       grind)
    | (have r₁ := eq10749 X0
       have r₂ := eq305 X0
       grind)
    | exact resolve eq10749 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq10749
  have eq10890 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10862 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10862
    | (have j0 := eq10862 (τ X0)
       grind)
    | exact resolve eq10862 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10862
  have eq11039 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10890 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq10890
    | (have j0 := eq10890 X0
       grind)
    | exact resolve eq10890 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10890
  have eq11055 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11039 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11039
    | (have j0 := eq11039 X0
       grind)
    | exact resolve eq11039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11039
  have eq11175 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (τ X0) X1
       have i₂ := eq11055 X0
       grind)
    | exact superpose eq11055 eq35
    | (have j1 := eq11055 X0
       grind)
    | (have r₁ := eq35 (τ X0) X1
       have r₂ := eq11055 X0
       grind)
    | exact resolve eq35 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq11055
  have eq11191 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11175
  have eq11219 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0
       have i₂ := eq11191 X0 X1
       grind)
    | exact superpose eq11191 eq314
    | (have j0 := eq314 X0
       have j1 := eq11191 X0 X1
       grind)
    | exact resolve eq314 eq11191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq11191
  have eq11371 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11219 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq11219 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq11219 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11219
  have eq12017 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (τ (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9821 (σ (k X0 X0))
       have i₂ := eq655 X0
       grind)
    | exact superpose eq655 eq9821
    | (have j0 := eq9821 (σ X0)
       have j1 := eq655 X0
       grind)
    | exact resolve eq9821 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq9821
  have eq12144 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (τ (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq12017 X0
       have j1 := eq197 X0
       grind)
    | (have r₁ := eq12017 X0
       have r₂ := eq197 X0
       grind)
    | exact resolve eq12017 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq12017
  have eq12173 : ∀ X0 : G, (k X0 X0) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12144 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq12144
    | (have j0 := eq12144 X0
       grind)
    | exact resolve eq12144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12144
  have eq12185 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12173 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12173
    | (have j0 := eq12173 X0
       grind)
    | exact resolve eq12173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12173
  have eq12565 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11371 (σ X0) X1
       have i₂ := eq12185 X0
       grind)
    | exact superpose eq12185 eq11371
    | (have j0 := eq11371 (σ X0) X1
       have j1 := eq12185 X0
       grind)
    | exact resolve eq11371 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371 eq12185
  have eq12579 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12565
  have eq12584 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12579 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12579
    | (have j0 := eq12579 X0 X1
       grind)
    | exact resolve eq12579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12579
  have eq12809 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12584 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12584
  have eq12810 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12809 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12809
  have eq13022 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12810 (σ X0)
       grind)
    | exact superpose eq12810 eq15
    | exact resolve eq15 eq12810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13087 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13022 X0
       have i₂ := eq12810 X0
       grind)
    | exact superpose eq12810 eq13022
    | exact resolve eq13022 eq12810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12810 eq13022
  have eq73516 : ∀ X0 X1 X2 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq955 X1 X2 X0
       grind)
    | exact superpose eq955 eq10
    | (have j1 := eq955 (k X0 X1) X1 (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq73707 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73516 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq73516
    | (have j0 := eq73516 X0 X1 X0
       grind)
    | exact resolve eq73516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73516
  have eq73956 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73707 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73707
  have eq73957 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73956 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73956
  have eq74222 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq73957 X0 (τ X1)
       grind)
    | exact superpose eq73957 eq19
    | (have j1 := eq73957 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq73957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq74278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq73957 (σ X0) (σ X1)
       grind)
    | exact superpose eq73957 eq15
    | (have j1 := eq73957 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq73957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73957
  have eq75413 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74222 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74222
    | exact resolve eq74222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74222
  have eq75738 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75413 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq75413
    | (have j0 := eq75413 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq75413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75413
  have eq77625 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74278 x y
       grind)
    | exact superpose eq74278 eq16
    | (have j1 := eq74278 x y
       grind)
    | exact resolve eq16 eq74278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74278
  have eq78012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq77625
       have i₂ := eq75738 y x
       grind)
    | exact superpose eq75738 eq77625
    | (have j1 := eq75738 (σ x) (σ y)
       grind)
    | (have r₁ := eq77625
       have r₂ := eq75738 y x
       grind)
    | (have r₁ := eq77625
       have r₂ := eq75738 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq77625
       have r₂ := eq75738 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq77625 eq75738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75738 eq77625
  have eq78019 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq78012
  have eq78024 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78019
       grind)
    | exact superpose eq78019 eq16
    | exact resolve eq16 eq78019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78019
  have eq78025 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq78024
       have r₂ := eq13087 x
       grind)
    | exact resolve eq78024 eq13087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78024
  have eq78390 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78025
       grind)
    | exact superpose eq78025 eq16
    | exact resolve eq16 eq78025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78391 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq78025
       grind)
    | exact superpose eq78025 eq10
    | exact resolve eq10 eq78025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78025
  have eq78588 : x = y := by
    first
    | (have i₁ := eq78391
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78391
    | exact resolve eq78391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78391
  have eq78589 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq78390
       have i₂ := eq13087 x
       grind)
    | exact superpose eq13087 eq78390
    | exact resolve eq78390 eq13087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13087 eq78390
  have eq78609 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq78589
       have i₂ := eq78588
       grind)
    | exact superpose eq78588 eq78589
    | exact resolve eq78589 eq78588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78588 eq78589
  have eq78610 : False := by grind
  exact eq78610

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq80 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq80 (σ X0)
       grind)
    | exact superpose eq80 eq15
    | exact resolve eq15 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq83
    | exact resolve eq83 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq83
  have eq296 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq296 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq296
    | (have j0 := eq296 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297 X1 X0
       have i₂ := eq296 X1 X0
       grind)
    | exact superpose eq296 eq297
    | (have j0 := eq297 X0 X1
       have j1 := eq296 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq297 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq297
  have eq1428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq407 x y
       grind)
    | exact superpose eq407 eq16
    | (have j1 := eq407 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq407 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq407 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq407 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq1447 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1428
  have eq1454 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1447
       grind)
    | exact superpose eq1447 eq10
    | exact resolve eq10 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1483 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1454
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1454
    | exact resolve eq1454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1484 : x = y := by grind
  clear eq1483
  have eq1487 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1484
       grind)
    | exact superpose eq1484 eq16
    | exact resolve eq16 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1488 : False := by grind
  exact eq1488
