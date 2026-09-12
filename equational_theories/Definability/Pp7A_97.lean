import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq270 (τ X0)
       grind)
    | exact superpose eq270 eq31
    | exact resolve eq31 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq294 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq287
    | exact resolve eq287 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq347 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq358 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq362 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       have j1 := eq359 X0 X1
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq359 X0 X1
       grind)
    | exact resolve eq358 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq359
  have eq407 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq347 y (σ x)
       grind)
    | exact superpose eq347 eq16
    | (have j1 := eq347 y (σ x)
       grind)
    | exact resolve eq16 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq424 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq417
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq417
    | exact resolve eq417 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq433 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq407 X1 X0
       grind)
    | exact superpose eq407 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq407 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq407 X0 X1
       grind)
    | exact resolve eq13 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq443 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq446 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq443 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq443 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq460 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq446 X0 (τ X1)
       grind)
    | exact superpose eq446 eq18
    | (have j1 := eq446 X0 (τ X1)
       grind)
    | exact resolve eq18 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq477 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq460 (τ X0) X1
       grind)
    | exact superpose eq460 eq17
    | (have j1 := eq460 (τ X0) X1
       grind)
    | exact resolve eq17 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq460
  have eq1241 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1234
    | (have j0 := eq1234 X0 X1
       grind)
    | exact resolve eq1234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1252 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1241 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1241
    | (have j0 := eq1241 X0 X1
       grind)
    | exact resolve eq1241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1253 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1252 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1252
    | (have j0 := eq1252 X0 X1
       grind)
    | exact resolve eq1252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1315 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1253 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1253
    | (have j0 := eq1253 X1 (σ X0)
       grind)
    | exact resolve eq1253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1752 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1315 X0 X0
       have i₂ := eq446 X0 (σ X0)
       grind)
    | exact superpose eq446 eq1315
    | (have j0 := eq1315 X1 X0
       have j1 := eq446 X0 (σ X1)
       grind)
    | exact resolve eq1315 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq1315
  have eq1789 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1752 X0 X1
       have j1 := eq477 X0 (σ X1)
       grind)
    | (have r₁ := eq1752 X0 X1
       have r₂ := eq477 X0 (σ X1)
       grind)
    | exact resolve eq1752 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq1752
  have eq2122 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1789 (σ X0) X1
       grind)
    | exact superpose eq1789 eq28
    | (have j1 := eq1789 (σ X0) X1
       grind)
    | exact resolve eq28 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1789
  have eq2133 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2122 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2122
    | (have j0 := eq2122 X0 X1
       grind)
    | exact resolve eq2122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2148 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2148 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2148
    | (have j0 := eq2148 X0 X1
       grind)
    | exact resolve eq2148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2259 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2157 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2157
    | (have j0 := eq2157 X1 (τ X0)
       grind)
    | exact resolve eq2157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2157 x y
       grind)
    | exact superpose eq2157 eq16
    | (have j1 := eq2157 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2157 x y
       grind)
    | exact resolve eq16 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2306 : x = (k x y) := by grind
  clear eq2272
  have eq2670 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X1 X0
       have i₂ := eq2259 X1 X0
       grind)
    | exact superpose eq2259 eq362
    | (have j0 := eq362 X1 X0
       have j1 := eq2259 X1 X0
       grind)
    | exact resolve eq362 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq2259
  have eq2684 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2670 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2761 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2684 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2684
    | exact resolve eq2684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2761 y x
       grind)
    | exact superpose eq2761 eq16
    | (have j1 := eq2761 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2761 y x
       grind)
    | exact resolve eq16 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq2908 : x = (M.op x y) := by grind
  clear eq2869
  have eq4400 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq424
       have i₂ := eq2908
       grind)
    | exact superpose eq2908 eq424
    | exact resolve eq424 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq4405 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq4400
  have eq4408 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4405
       have i₂ := eq2306
       grind)
    | exact superpose eq2306 eq4405
    | exact resolve eq4405 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306 eq4405
  have eq4415 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4408
       grind)
    | exact superpose eq4408 eq16
    | exact resolve eq16 eq4408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4408
  have eq4442 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4415
       have i₂ := eq2908
       grind)
    | exact superpose eq2908 eq4415
    | exact resolve eq4415 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908 eq4415
  have eq4443 : False := by grind
  exact eq4443

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq65 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq82 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq83 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq83
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq87
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq82
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq82
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq66
  have eq660 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq542 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq8882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8882
    | exact resolve eq8882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8882
  have eq8894 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq8883
       have r₂ := eq28
       grind)
    | exact resolve eq8883 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8883
  have eq8898 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8894
    | exact resolve eq8894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8894
  have eq8907 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8898 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8898
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8898
       grind)
    | exact resolve eq12 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8898
  have eq12670 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8907
    | (have j0 := eq8907 (σ x)
       grind)
    | (have r₁ := eq8907 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq8907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8907
  have eq12671 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq12670
  have eq12672 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq12671
  have eq12680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq12672 eq97
    | exact resolve eq97 eq12672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12672
  have eq12690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12680
  have eq12693 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12690
       have r₂ := eq28
       grind)
    | exact resolve eq12690 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12690
  have eq12696 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq12693
       grind)
    | exact superpose eq12693 eq88
    | exact resolve eq88 eq12693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12703 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12693
       grind)
    | exact superpose eq12693 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12693
       grind)
    | exact resolve eq12 eq12693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12693
  have eq12719 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12696
    | exact resolve eq12696 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12696
  have eq19093 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12703 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12703
    | (have j0 := eq12703 x
       grind)
    | (have r₁ := eq12703 x
       have r₂ := eq19
       grind)
    | exact resolve eq12703 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12703
  have eq19094 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq19093
  have eq19095 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19094
  have eq19106 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq660 x y
       have i₂ := eq19095
       grind)
    | exact superpose eq19095 eq660
    | (have j0 := eq660 x y
       grind)
    | exact resolve eq660 eq19095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq19095
  have eq19110 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19106
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq19106
    | exact resolve eq19106 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19106
  have eq19120 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq19110
    | exact resolve eq19110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19110
  have eq19123 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19120
       have r₂ := eq12719
       grind)
    | exact resolve eq19120 eq12719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19120
  have eq19124 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19123
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq19123
    | exact resolve eq19123 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq19123
  have eq19125 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19124
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19124
    | exact resolve eq19124 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19124
  have eq19126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19125
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19125
    | exact resolve eq19125 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19125
  have eq19127 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19126
    | exact resolve eq19126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19126
  have eq19128 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19127
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19127
    | exact resolve eq19127 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19127
  have eq19129 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19128
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19128
    | exact resolve eq19128 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19128
  have eq19130 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19129
  have eq19190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19130 eq12719
    | exact resolve eq12719 eq19130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12719 eq19130
  have eq19234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19190
  have eq19242 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19234
       have r₂ := eq28
       grind)
    | exact resolve eq19234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234
  have eq19245 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq19242 eq30
    | exact resolve eq30 eq19242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19242
  have eq19361 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq19245
    | exact resolve eq19245 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19245
  have eq19362 : x = y := by grind
  clear eq19361
  have eq19383 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19362
       grind)
    | exact superpose eq19362 eq19
    | exact resolve eq19 eq19362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19384 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq19362
       grind)
    | exact superpose eq19362 eq25
    | exact resolve eq25 eq19362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19362
  have eq19505 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19384
    | exact resolve eq19384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19384
  have eq19524 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19505 eq27
    | exact resolve eq27 eq19505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19505
  have eq19717 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19524 eq65
    | exact resolve eq65 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19524
  have eq19737 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19717
       have i₂ := eq19383
       grind)
    | exact superpose eq19383 eq19717
    | exact resolve eq19717 eq19383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19383 eq19717
  have eq19751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19737 eq15
    | exact resolve eq15 eq19737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19737
  have eq19828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19751
    | exact resolve eq19751 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19751
  have eq19849 : False := by grind
  exact eq19849

/-- `Equation633`: `x = x ◇ (y ◇ ((x ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation633 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law633 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law633.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq123 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq775 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq3744 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq123 X1 X0
       grind)
    | exact superpose eq123 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq123 X1 X0
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq123 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq123 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq13 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq3762 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3744 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3763 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3762 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3762
  have eq3973 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3763 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3763
    | exact resolve eq3763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763
  have eq4031 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3973 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3973
    | (have j0 := eq3973 X0 X1
       grind)
    | exact resolve eq3973 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq4078 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq4031 X1 X0
       grind)
    | exact superpose eq4031 eq10
    | (have j1 := eq4031 X1 X0
       grind)
    | exact resolve eq10 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4127 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4078 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4078
    | (have j0 := eq4078 X0 X1
       grind)
    | exact resolve eq4078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4184 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq4127 (σ X0) X1
       grind)
    | exact superpose eq4127 eq37
    | (have j1 := eq4127 (σ X0) X1
       grind)
    | exact resolve eq37 eq4127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4127
  have eq4483 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq4184 X1 (σ X0)
       grind)
    | exact superpose eq4184 eq28
    | (have j1 := eq4184 X1 (σ X0)
       grind)
    | exact resolve eq28 eq4184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4184
  have eq4545 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4483 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4483
    | (have j0 := eq4483 X0 X1
       grind)
    | exact resolve eq4483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4483
  have eq4580 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4545 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4545
    | (have j0 := eq4545 X0 X1
       grind)
    | exact resolve eq4545 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4590 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4580 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4580
    | (have j0 := eq4580 X0 X1
       grind)
    | exact resolve eq4580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4797 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4590 X1 X0
       grind)
    | exact superpose eq4590 eq11
    | (have j1 := eq4590 X1 X0
       grind)
    | exact resolve eq11 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq5710 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4797 x y
       grind)
    | exact superpose eq4797 eq16
    | (have j1 := eq4797 x y
       grind)
    | exact resolve eq16 eq4797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq5743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5710
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5710
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5710
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5710
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5710 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5744 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5710
       have i₂ := eq4031 y x
       grind)
    | exact superpose eq4031 eq5710
    | (have j1 := eq4031 y x
       grind)
    | (have r₁ := eq5710
       have r₂ := eq4031 y x
       grind)
    | (have r₁ := eq5710
       have r₂ := eq4031 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5710
       have r₂ := eq4031 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5710 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031 eq5710
  have eq5747 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5744
  have eq5748 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5747
  have eq5749 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5743
  have eq5750 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5749
  have eq5754 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5748
       grind)
    | exact superpose eq5748 eq16
    | exact resolve eq16 eq5748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5748
  have eq5755 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5754
       have r₂ := eq22 x
       grind)
    | exact resolve eq5754 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5754
  have eq5760 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq775 x y
       have i₂ := eq5755
       grind)
    | exact superpose eq5755 eq775
    | (have j0 := eq775 x y
       grind)
    | exact resolve eq775 eq5755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq5755
  have eq5767 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5760
  have eq5768 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5767
  have eq5773 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5750
       grind)
    | exact superpose eq5750 eq16
    | exact resolve eq16 eq5750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5750
  have eq5774 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5773
       have r₂ := eq22 x
       grind)
    | exact resolve eq5773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5773
  have eq5786 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5768
       grind)
    | exact superpose eq5768 eq16
    | exact resolve eq16 eq5768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5768
  have eq5814 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5786
       have i₂ := eq5774
       grind)
    | exact superpose eq5774 eq5786
    | exact resolve eq5786 eq5774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5774 eq5786
  have eq5815 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq5814
  have eq5816 : (σ x) = (σ y) := by grind
  clear eq5815
  have eq5817 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5816
       grind)
    | exact superpose eq5816 eq16
    | exact resolve eq16 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5818 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5816
       grind)
    | exact superpose eq5816 eq10
    | exact resolve eq10 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5816
  have eq5872 : x = y := by
    first
    | (have i₁ := eq5818
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5818
    | exact resolve eq5818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5818
  have eq5873 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5817
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5817
    | exact resolve eq5817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5817
  have eq5874 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5873
       have i₂ := eq5872
       grind)
    | exact superpose eq5872 eq5873
    | exact resolve eq5873 eq5872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872 eq5873
  have eq5875 : False := by grind
  exact eq5875

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq165 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165 X0 X1
       have j1 := eq53 X1 X0
       grind)
    | (have r₁ := eq165 X0 X0
       have r₂ := eq53 X0 X0
       grind)
    | (have r₁ := eq165 X1 X0
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq165 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq165
  have eq402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq172 (σ X0) (σ X1)
       grind)
    | exact superpose eq172 eq15
    | exact resolve eq15 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq172 X0 X1
       grind)
    | exact superpose eq172 eq402
    | exact resolve eq402 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq402
  have eq412 : False := by grind
  exact eq412

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq74
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq74
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq100
    | exact resolve eq100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq101
  have eq152 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq154 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq157 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq152
    | (have j0 := eq152 X0 X1
       grind)
    | exact resolve eq152 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq802 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq844 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq802
    | (have j0 := eq802 X0 X1
       grind)
    | exact resolve eq802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq871 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq16
    | (have j1 := eq157 x y
       grind)
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq4681 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq871
       have i₂ := eq844 y x
       grind)
    | exact superpose eq844 eq871
    | (have j1 := eq844 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq871
       have r₂ := eq844 y x
       grind)
    | (have r₁ := eq871
       have r₂ := eq844 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq871
       have r₂ := eq844 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq871 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq871
  have eq4682 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq4681
  have eq4684 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4682
       grind)
    | exact superpose eq4682 eq16
    | exact resolve eq16 eq4682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4685 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4684
       have r₂ := eq81 x
       grind)
    | exact resolve eq4684 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq4691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq4685
       grind)
    | exact superpose eq4685 eq104
    | exact resolve eq104 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685
  have eq4700 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4691
       have r₂ := eq16
       grind)
    | exact resolve eq4691 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4691
  have eq4703 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4700
       grind)
    | exact superpose eq4700 eq10
    | exact resolve eq10 eq4700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4700
  have eq4753 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4703
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4703
    | exact resolve eq4703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4756 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4753
       grind)
    | exact superpose eq4753 eq16
    | exact resolve eq16 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753
  have eq4757 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4756
       have r₂ := eq81 x
       grind)
    | exact resolve eq4756 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq4756
  have eq4763 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq4757
       grind)
    | exact superpose eq4757 eq10
    | exact resolve eq10 eq4757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4757
  have eq4813 : y = (M.op x x) := by
    first
    | (have i₁ := eq4763
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4763
    | exact resolve eq4763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4763
  have eq4825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq4813
       grind)
    | exact superpose eq4813 eq104
    | exact resolve eq104 eq4813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq4813
  have eq4833 : False := by grind
  exact eq4833

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pxx_y_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq56
    | exact resolve eq56 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq1344 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 X1 X0
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1379 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op X3 (M.op X3 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1344 x X2 X3
       have i₂ := eq1344 x X2 X0
       grind)
    | exact superpose eq1344 eq1344
    | exact resolve eq1344 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq1344 x X2 X0
       grind)
    | exact superpose eq1344 eq9
    | exact resolve eq9 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1456 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1391 X0 (M.op X0 X0)
       have i₂ := eq1391 X0 X0
       grind)
    | exact superpose eq1391 eq1391
    | exact resolve eq1391 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X0 (M.op X0 X2)) X2
       have i₂ := eq1391 X0 X2
       grind)
    | exact superpose eq1391 eq54
    | exact resolve eq54 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1467 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1462 X2 X0 X2
       have i₂ := eq1391 X0 X2
       grind)
    | (have i₁ := eq1462 X0 X1 X2
       have i₂ := eq1391 X0 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq1391 eq1462
    | exact resolve eq1462 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1482 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1456 X0
       grind)
    | exact superpose eq1456 eq9
    | exact resolve eq9 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq1502 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1482 (τ X0) X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq1482
    | exact resolve eq1482 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1572 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1379 X2 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq1482 X0 X1
       grind)
    | exact superpose eq1482 eq1379
    | exact resolve eq1379 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1578 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1379 X2 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq1391 X1 X0
       grind)
    | exact superpose eq1391 eq1379
    | exact resolve eq1379 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq1391
  have eq1895 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1467 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq1482 X0 X1
       grind)
    | exact superpose eq1482 eq1467
    | exact resolve eq1467 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1959 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1895 X0 X1 x
       have i₂ := eq1572 X0 X1 x
       grind)
    | exact superpose eq1572 eq1895
    | exact resolve eq1895 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq2312 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1482 X0 X1
       have i₂ := eq1959 X0 X1
       grind)
    | (have i₁ := eq1482 X0 X0
       have i₂ := eq1959 X0 X0
       grind)
    | exact superpose eq1959 eq1482
    | exact resolve eq1482 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq3818 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X1)))) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1578 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq1578 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1578
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq1578 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq3983 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3818 X0 X1 x
       have i₂ := eq1572 X1 X1 x
       grind)
    | exact superpose eq1572 eq3818
    | (have j0 := eq3818 X0 X1 x
       grind)
    | exact resolve eq3818 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572 eq3818
  have eq3984 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3983 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq18499 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X2 (M.op X2 (τ (M.op X1 X1)))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1502 X0 X2
       have i₂ := eq3984 X0 X1
       grind)
    | (have i₁ := eq1502 X1 X1
       have i₂ := eq3984 X0 X1
       grind)
    | exact superpose eq3984 eq1502
    | (have j1 := eq3984 X0 X1
       grind)
    | exact resolve eq1502 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18532 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2312 X0 X0
       have i₂ := eq3984 X0 X1
       grind)
    | (have i₁ := eq2312 X1 X1
       have i₂ := eq3984 X0 X1
       grind)
    | exact superpose eq3984 eq2312
    | (have j1 := eq3984 X0 X1
       grind)
    | exact resolve eq2312 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312 eq3984
  have eq18592 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18532 X0 X1
       have i₂ := eq1482 X1 X0
       grind)
    | exact superpose eq1482 eq18532
    | (have j0 := eq18532 X0 X1
       grind)
    | exact resolve eq18532 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq18532
  have eq18599 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18499 X0 X1 x
       have i₂ := eq1502 X1 x
       grind)
    | exact superpose eq1502 eq18499
    | (have j0 := eq18499 X0 X1 x
       grind)
    | exact resolve eq18499 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq18499
  have eq18690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18599 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18599
    | (have j0 := eq18599 (σ X0) (σ X1)
       grind)
    | exact resolve eq18599 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18599
  have eq18770 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18690 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq18690
    | (have j0 := eq18690 X0 X1
       grind)
    | exact resolve eq18690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18690
  have eq18776 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18770 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18770
    | (have j0 := eq18770 X0 X1
       grind)
    | exact resolve eq18770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18770
  have eq18962 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq18776 y x
       grind)
    | exact superpose eq18776 eq16
    | (have j1 := eq18776 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq18776 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq18776 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq18776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18776
  have eq19030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq18962
       have i₂ := eq18592 y x
       grind)
    | exact superpose eq18592 eq18962
    | (have j1 := eq18592 x y
       grind)
    | (have r₁ := eq18962
       have r₂ := eq18592 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq18962
       have r₂ := eq18592 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq18962 eq18592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18592 eq18962
  have eq19035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq19030
  have eq19036 : x = y := by grind
  clear eq19035
  have eq19039 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19036
       grind)
    | exact superpose eq19036 eq16
    | exact resolve eq16 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19040 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19039
       have i₂ := eq60 x
       grind)
    | exact superpose eq60 eq19039
    | (have r₁ := eq19039
       have r₂ := eq60 x
       grind)
    | exact resolve eq19039 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq19039
  have eq19041 : False := by grind
  exact eq19041

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq107 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq109 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq43
    | exact resolve eq43 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq73
    | exact resolve eq73 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq113
    | exact resolve eq113 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq99
    | exact resolve eq99 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq126
    | exact resolve eq126 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq126
  have eq750 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1079 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq750 X1 x X3
       have i₂ := eq750 X1 x X0
       grind)
    | exact superpose eq750 eq750
    | exact resolve eq750 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq750 X1 x X0
       grind)
    | exact superpose eq750 eq14
    | exact resolve eq14 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X2 X0) X2
       have i₂ := eq750 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq750 eq53
    | exact resolve eq53 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq1109 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1102 X0 X1 X2
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq1102
    | exact resolve eq1102 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1102
  have eq1124 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1091 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1091
    | (have j0 := eq1091 x y
       grind)
    | exact resolve eq1091 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq1091
    | (have j0 := eq1091 (σ x) (σ y)
       grind)
    | exact resolve eq1091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1091 X0 (M.op X0 X0)
       have i₂ := eq1091 X0 X0
       grind)
    | exact superpose eq1091 eq1091
    | exact resolve eq1091 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1871 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1124 eq1079
    | exact resolve eq1079 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1875 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1125 eq1079
    | exact resolve eq1079 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq2107 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1109 X0 X1 X0
       have i₂ := eq1130 X0
       grind)
    | exact superpose eq1130 eq1109
    | exact resolve eq1109 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq1130
  have eq3916 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1871 x
       have i₂ := eq1079 x sF0 x
       grind)
    | (have i₁ := eq1871 x
       have i₂ := eq1079 X0 sF0 x
       grind)
    | exact superpose eq1079 eq1871
    | exact resolve eq1871 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq3971 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1875 sF2
       have i₂ := eq1079 sF2 sF4 x
       grind)
    | (have i₁ := eq1875 sF2
       have i₂ := eq1079 X0 sF4 sF2
       grind)
    | exact superpose eq1079 eq1875
    | exact resolve eq1875 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq1875
  have eq17342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17342
    | exact resolve eq17342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17342
  have eq17359 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17349
       have r₂ := eq27
       grind)
    | exact resolve eq17349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17349
  have eq17362 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17359
    | exact resolve eq17359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17359
  have eq17364 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17362
    | exact resolve eq17362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17362
  have eq17366 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17364 eq107
    | (have r₁ := eq107
       have r₂ := eq17364
       grind)
    | exact resolve eq107 eq17364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq17364
  have eq17412 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq17366
  have eq17413 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq17412
  have eq17445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17413 eq94
    | exact resolve eq94 eq17413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq17413
  have eq17458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17445
  have eq17460 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17458
       have r₂ := eq27
       grind)
    | exact resolve eq17458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17458
  have eq17462 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq17460
       grind)
    | exact superpose eq17460 eq106
    | (have r₁ := eq106
       have r₂ := eq17460
       grind)
    | exact resolve eq106 eq17460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq17463 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq17460
       grind)
    | exact superpose eq17460 eq118
    | exact resolve eq118 eq17460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq17460
  have eq17509 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17462
  have eq17510 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17509
  have eq17522 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17463
    | exact resolve eq17463 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17463
  have eq17738 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq17510
       grind)
    | exact superpose eq17510 eq72
    | exact resolve eq72 eq17510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq17510
  have eq17764 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17738
    | exact resolve eq17738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17738
  have eq18057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17764 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq17764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17764
  have eq18066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18057
    | exact resolve eq18057 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18057
  have eq18076 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18066
       have r₂ := eq27
       grind)
    | exact resolve eq18066 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18066
  have eq18079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18076
    | exact resolve eq18076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18076
  have eq18081 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18079
    | exact resolve eq18079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18079
  have eq18082 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18081
  have eq18235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18082 eq17522
    | exact resolve eq17522 eq18082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17522 eq18082
  have eq18276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18235
  have eq18286 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18276
       have r₂ := eq27
       grind)
    | exact resolve eq18276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18276
  have eq18306 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18286 eq3971
    | exact resolve eq3971 eq18286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971 eq18286
  have eq18313 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18306 x
       have i₂ := eq1091 x sF2
       grind)
    | exact superpose eq1091 eq18306
    | exact resolve eq18306 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306
  have eq18460 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18313 eq127
    | exact resolve eq127 eq18313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq18313
  have eq18539 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq18460
    | exact resolve eq18460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18460
  have eq18982 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2107 y y
       have i₂ := eq18539
       grind)
    | exact superpose eq18539 eq2107
    | exact resolve eq2107 eq18539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18539
  have eq18986 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18982
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18982
    | exact resolve eq18982 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18982
  have eq18987 : x = (M.op x y) := by grind
  clear eq18986
  have eq19019 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18987 eq20
    | exact resolve eq20 eq18987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19086 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq18987 eq3916
    | exact resolve eq3916 eq18987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916 eq18987
  have eq19093 : x = (M.op y y) := by
    first
    | (have i₁ := eq19086 x
       have i₂ := eq1091 x x
       grind)
    | exact superpose eq1091 eq19086
    | exact resolve eq19086 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq19086
  have eq19152 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19019
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19019
    | exact resolve eq19019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19019
  have eq19183 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19152 eq26
    | exact resolve eq26 eq19152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19356 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq19093
       grind)
    | exact superpose eq19093 eq117
    | exact resolve eq117 eq19093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq19093
  have eq19440 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19356
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19356
    | exact resolve eq19356 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19356
  have eq19457 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19152 eq19440
    | exact resolve eq19440 eq19152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19152 eq19440
  have eq20035 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19457 eq2107
    | exact resolve eq2107 eq19457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq19457
  have eq20039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19183 eq20035
    | exact resolve eq20035 eq19183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19183 eq20035
  have eq20070 : False := by grind
  exact eq20070

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq63 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
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
  clear eq22 eq36
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq83 y x
       grind)
    | exact superpose eq83 eq75
    | (have j1 := eq83 y x
       grind)
    | exact resolve eq75 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq114
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq83
    | (have j0 := eq83 (σ y) (σ x)
       grind)
    | exact resolve eq83 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq142 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq64
    | exact resolve eq64 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq143 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq27
    | exact resolve eq27 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq68
    | (have r₁ := eq68
       have r₂ := eq128
       grind)
    | exact resolve eq68 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq128
  have eq352 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq351
  have eq353 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq352
       have r₂ := eq142
       grind)
    | exact resolve eq352 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq352
  have eq356 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq353 eq115
    | exact resolve eq115 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq353
  have eq360 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq356
  have eq365 : y = (M.op x y) := by
    first
    | (have r₁ := eq360
       have r₂ := eq143
       grind)
    | exact resolve eq360 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq360
  have eq368 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq365 eq20
    | exact resolve eq20 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq371 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq365 eq63
    | exact resolve eq63 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq372 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq365 eq67
    | (have r₁ := eq67
       have r₂ := eq365
       grind)
    | exact resolve eq67 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq365
  have eq377 : x = y ∨ y = (k y x) := by grind
  clear eq372
  have eq383 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq368
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq368
    | exact resolve eq368 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq385 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq383 eq26
    | exact resolve eq26 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq539 : y = (k y x) := by
    first
    | (have r₁ := eq377
       have r₂ := eq371
       grind)
    | exact resolve eq377 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq377
  have eq543 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq539
       grind)
    | exact superpose eq539 eq75
    | exact resolve eq75 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq539
  have eq550 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq383 eq543
    | exact resolve eq543 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq552 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq550
    | exact resolve eq550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq550
  have eq553 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq383 eq552
    | exact resolve eq552 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq552
  have eq556 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq553 eq83
    | (have j0 := eq83 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq83 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq553
  have eq557 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq556
  have eq559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385 eq557
    | exact resolve eq557 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq557
  have eq562 : False := by grind
  exact eq562
