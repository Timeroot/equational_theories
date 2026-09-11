import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq347 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq423 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq432 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq347 X1 X0
       grind)
    | exact superpose eq347 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq347 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq347 X0 X1
       grind)
    | exact resolve eq13 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq442 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq447 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq442 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq442 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq504 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq447
    | exact resolve eq447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq504 (τ X1) X0
       grind)
    | exact superpose eq504 eq18
    | (have j1 := eq504 (τ X1) X0
       grind)
    | exact resolve eq18 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq572 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq504 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq1023 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq555 (τ X0) X1
       grind)
    | exact superpose eq555 eq17
    | (have j1 := eq555 (τ X0) X1
       grind)
    | exact resolve eq17 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq555
  have eq1032 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1023
    | (have j0 := eq1023 X0 X1
       grind)
    | exact resolve eq1023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1043 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1032 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1032
    | (have j0 := eq1032 X0 X1
       grind)
    | exact resolve eq1032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1044 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1043 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1043
    | (have j0 := eq1043 X0 X1
       grind)
    | exact resolve eq1043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1100 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1044 X1 X0
       have i₂ := eq423 X0 X1
       grind)
    | exact superpose eq423 eq1044
    | (have j1 := eq423 X1 X0
       grind)
    | exact resolve eq1044 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1044 X0 (σ X1)
       have i₂ := eq447 X0 X1
       grind)
    | exact superpose eq447 eq1044
    | (have j0 := eq1044 X0 (σ X1)
       have j1 := eq447 X0 X1
       grind)
    | exact resolve eq1044 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq1044
  have eq1139 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1166 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1101 X0 X1
       have j1 := eq572 X0 (σ X1)
       grind)
    | (have r₁ := eq1101 X0 X1
       have r₂ := eq572 X0 (σ X1)
       grind)
    | exact resolve eq1101 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1101
  have eq1184 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1166 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1166
    | (have j0 := eq1166 X0 X1
       grind)
    | exact resolve eq1166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1288 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1139 (σ x) (σ y)
       grind)
    | exact superpose eq1139 eq16
    | (have j1 := eq1139 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1323 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1288
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1288
    | exact resolve eq1288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1323
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1323
    | exact resolve eq1323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1353 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq1347
       have r₂ := eq16
       grind)
    | exact resolve eq1347 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq2597 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1184 (σ X0) X1
       grind)
    | exact superpose eq1184 eq28
    | (have j1 := eq1184 (σ X0) X1
       grind)
    | exact resolve eq28 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1184
  have eq2610 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2597 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2597
    | (have j0 := eq2597 X0 X1
       grind)
    | exact resolve eq2597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq2625 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2610 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2610
    | (have j0 := eq2610 X0 X1
       grind)
    | exact resolve eq2610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq2633 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2625 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2625
    | (have j0 := eq2625 X0 X1
       grind)
    | exact resolve eq2625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2633 x y
       grind)
    | exact superpose eq2633 eq16
    | (have j1 := eq2633 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2633 x y
       grind)
    | exact resolve eq16 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq2688 : x = (k x y) := by grind
  clear eq2662
  have eq2732 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423 y x
       have i₂ := eq2688
       grind)
    | exact superpose eq2688 eq423
    | (have j0 := eq423 y x
       grind)
    | exact resolve eq423 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq2688
  have eq2735 : x = (M.op x y) := by grind
  clear eq2732
  have eq2740 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1353
       have i₂ := eq2735
       grind)
    | exact superpose eq2735 eq1353
    | exact resolve eq1353 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353 eq2735
  have eq2748 : False := by grind
  exact eq2748

/-- `Equation1874`: `x = (x ◇ (y ◇ z)) ◇ (y ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_x_pyx_Equation1874 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X3)) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 (k X0 x))) = (k (σ X1) (k (σ X0) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq10
    | exact resolve eq10 eq39
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 X4)) X1 x X2
       have i₂ := eq16 X0 X1 X4 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq182 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) ≠ X0 ∨ (k (M.op X1 X3) (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X1 X3) (M.op X0 (M.op X1 X2))
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X1 X3) (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq13 (M.op X1 X3) (M.op (M.op X1 X3) (M.op X1 X2))
       have r₂ := eq16 (M.op X1 X3) X1 X2 X3
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 X0 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X0 (M.op x y)) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq194 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq679 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq184 eq187
    | exact resolve eq187 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq187
  have eq733 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq679 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq679
    | (have j0 := eq679 y x
       grind)
    | exact resolve eq679 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq679
    | (have j0 := eq679 (σ y) (σ x)
       grind)
    | exact resolve eq679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (M.op X0 X2) X2 X3
       have i₂ := eq679 X2 X0
       grind)
    | exact superpose eq679 eq177
    | exact resolve eq177 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X3)) X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) X3 X2
       have i₂ := eq679 X2 X0
       grind)
    | exact superpose eq679 eq16
    | exact resolve eq16 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | exact superpose eq733 eq177
    | exact resolve eq177 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq733 eq16
    | exact resolve eq16 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq734 eq177
    | exact resolve eq177 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq836 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq863 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (k X0 X1)) (M.op X1 X3)) = X2 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X1 X0 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq938 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq866 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq866 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq866 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq866 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq2275 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq861
       grind)
    | exact superpose eq861 eq39
    | exact resolve eq39 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2276 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2275
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2275
    | exact resolve eq2275 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2278 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2276
    | exact resolve eq2276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq2436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2278 eq863
    | exact resolve eq863 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2443 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2436
       have r₂ := eq27
       grind)
    | exact resolve eq2436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2449 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2443 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2443
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2443
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2443
       grind)
    | exact resolve eq12 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443
  have eq2467 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2449
  have eq2477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2467
    | exact resolve eq2467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq2478 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2477
  have eq2528 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2478 eq141
    | exact resolve eq141 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2478
  have eq2533 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2528
    | exact resolve eq2528 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2536 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq861 eq2533
    | exact resolve eq2533 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq2537 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2536
  have eq2541 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2537
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq2537
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq2537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2543 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2537
       grind)
    | exact superpose eq2537 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2537
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2537
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2537
       grind)
    | exact resolve eq12 eq2537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2537
       grind)
    | exact superpose eq2537 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2537
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2537
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2537
       grind)
    | exact resolve eq13 eq2537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2560 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2544
  have eq2561 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2543
  have eq2570 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2560
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2560
    | exact resolve eq2560 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2571 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2561
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2561
    | exact resolve eq2561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2572 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2571
  have eq2574 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq2541
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq2541
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq2541
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2575 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2574
       have r₂ := eq834
       grind)
    | exact resolve eq2574 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2576 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2537 eq2575
    | exact resolve eq2575 eq2537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537 eq2575
  have eq2635 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2570
       grind)
    | exact superpose eq2570 eq40
    | exact resolve eq40 eq2570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570
  have eq2638 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2635
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2635
    | exact resolve eq2635 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635
  have eq2640 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2638
    | exact resolve eq2638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2645 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2572
       grind)
    | exact superpose eq2572 eq39
    | exact resolve eq39 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2652 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2645
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2645
    | exact resolve eq2645 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2688 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2652 eq863
    | exact resolve eq863 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2696 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2688
  have eq2718 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2696
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq2696
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq2696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2696 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2696
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2696
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2696
       grind)
    | exact resolve eq13 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2737 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2721
  have eq2747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2737
    | exact resolve eq2737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2749 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq2718
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq2718
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq2718
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq2718 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq2750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2640 eq2747
    | exact resolve eq2747 eq2640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640 eq2747
  have eq2751 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2749
       have r₂ := eq836
       grind)
    | exact resolve eq2749 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq2749
  have eq2752 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2750
       have r₂ := eq27
       grind)
    | exact resolve eq2750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2753 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2752 eq27
    | exact resolve eq27 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2756 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2752 eq182
    | (have r₁ := eq182
       have r₂ := eq2752
       grind)
    | exact resolve eq182 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2762 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2752 eq764
    | exact resolve eq764 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2767 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2756
  have eq2843 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) X1)) (k (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2767 eq16
    | exact resolve eq16 eq2767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2867 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (k (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2762 eq2843
    | exact resolve eq2843 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762 eq2843
  have eq3288 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2767 eq2867
    | exact resolve eq2867 eq2767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2867
  have eq3325 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq3288
  have eq3495 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3325 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3497 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3325 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq3325
       grind)
    | exact resolve eq13 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq3513 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3495
  have eq3526 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3513
       have r₂ := eq3497
       grind)
    | exact resolve eq3513 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497 eq3513
  have eq3580 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2278 eq3526
    | exact resolve eq3526 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3586 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq3580
  have eq4119 : x ≠ x ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2576 eq911
    | (have j0 := eq911 (M.op x y) x
       grind)
    | (have r₁ := eq911 (M.op x y) x
       have r₂ := eq2576
       grind)
    | exact resolve eq911 eq2576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq4120 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq4119
  have eq4122 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2752 eq4120
    | exact resolve eq4120 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4123 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4122
  have eq4188 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq183 (M.op X0 X1) X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq4189 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4188 X0 X1 X2
       have i₂ := eq741 X0 (M.op X0 X1) X1 (M.op X0 X2)
       grind)
    | exact superpose eq741 eq4188
    | exact resolve eq4188 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq4188
  have eq4236 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4123 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq4123
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq4123
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4123
       grind)
    | exact resolve eq13 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123
  have eq4255 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4236
  have eq4509 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2751 eq152
    | exact resolve eq152 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2751
  have eq4525 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq4509
    | exact resolve eq4509 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4509
  have eq4559 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4525 eq2767
    | exact resolve eq2767 eq4525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq4568 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4525 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4525
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4525
       grind)
    | exact resolve eq13 eq4525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4525
  have eq4587 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4568
  have eq4595 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4559
  have eq4606 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq4587
    | exact resolve eq4587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4612 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq2752 eq4606
    | exact resolve eq4606 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606
  have eq4693 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4595 eq2278
    | exact resolve eq2278 eq4595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278
  have eq4703 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4595 eq107
    | exact resolve eq107 eq4595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4595
  have eq4720 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4693
  have eq4725 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq4703
    | exact resolve eq4703 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4726 : x = (k x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4720
       have r₂ := eq834
       grind)
    | exact resolve eq4720 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4824 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq4725
       grind)
    | exact superpose eq4725 eq861
    | exact resolve eq861 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq4725
  have eq4832 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4824
  have eq4842 : x = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4832
       have r₂ := eq834
       grind)
    | exact resolve eq4832 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4832
  have eq4856 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4726
       grind)
    | exact superpose eq4726 eq40
    | exact resolve eq40 eq4726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4860 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq911 y x
       have i₂ := eq4726
       grind)
    | exact superpose eq4726 eq911
    | (have j0 := eq911 y x
       grind)
    | (have r₁ := eq911 y x
       have r₂ := eq4726
       grind)
    | exact resolve eq911 eq4726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4726
  have eq4861 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4860
  have eq4862 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4861
  have eq4866 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4862
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4862
    | exact resolve eq4862 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862
  have eq4870 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4856
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4856
    | exact resolve eq4856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq4877 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4866
       grind)
    | exact superpose eq4866 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4866
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4866
       grind)
    | exact resolve eq13 eq4866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4866
  have eq4896 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4877
  have eq4906 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4896
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4896
    | exact resolve eq4896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq5772 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4906
       grind)
    | exact superpose eq4906 eq40
    | exact resolve eq40 eq4906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5779 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5772
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5772
    | exact resolve eq5772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5772
  have eq5781 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq5779
    | exact resolve eq5779 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5779
  have eq5823 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5781 eq4612
    | exact resolve eq4612 eq5781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612 eq5781
  have eq5835 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5823
  have eq5844 : y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5835
       have r₂ := eq2753
       grind)
    | exact resolve eq5835 eq2753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753 eq5835
  have eq5848 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4906 eq5844
    | exact resolve eq5844 eq4906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4906 eq5844
  have eq5850 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5848 eq28
    | exact resolve eq28 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5848
  have eq5879 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq5850
    | exact resolve eq5850 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5850
  have eq5880 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5879
  have eq5883 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5880
       grind)
    | exact superpose eq5880 eq18
    | exact resolve eq18 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5884 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5880
       grind)
    | exact superpose eq5880 eq24
    | exact resolve eq24 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5887 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181
       have i₂ := eq5880
       grind)
    | exact superpose eq5880 eq181
    | (have r₁ := eq181
       have r₂ := eq5880
       grind)
    | exact resolve eq181 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5888 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq733
       have i₂ := eq5880
       grind)
    | exact superpose eq5880 eq733
    | exact resolve eq733 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5893 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq5887
  have eq5896 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5884
    | exact resolve eq5884 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5884
  have eq5984 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5888 eq11
    | exact resolve eq11 eq5888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq6010 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5984
  have eq6060 : ∀ X0 : G, (M.op (M.op X0 x) (k (M.op x y) x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5893 eq761
    | exact resolve eq761 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq6078 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5893 eq679
    | exact resolve eq679 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6622 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5893 eq6060
    | exact resolve eq6060 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060
  have eq6653 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by grind
  clear eq6622
  have eq7002 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6653 eq11
    | exact resolve eq11 eq6653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7004 : (M.op x y) ≠ (k (M.op x y) x) ∨ (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6653 eq13
    | exact resolve eq13 eq6653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6653
  have eq7028 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq7002
  have eq7045 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7028
       have r₂ := eq7004
       grind)
    | exact resolve eq7028 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004 eq7028
  have eq7414 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4842
       grind)
    | exact superpose eq4842 eq40
    | exact resolve eq40 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq7434 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7414
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7414
    | exact resolve eq7414 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414
  have eq7438 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5880 eq7434
    | exact resolve eq7434 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7434
  have eq7455 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4870 eq938
    | (have j0 := eq938 (σ x) (σ y)
       grind)
    | (have r₁ := eq938 (σ x) (σ y)
       have r₂ := eq4870
       grind)
    | exact resolve eq938 eq4870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq7458 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq7455
  have eq7467 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq7458
    | exact resolve eq7458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458
  have eq7474 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq7467
    | exact resolve eq7467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7467
  have eq7478 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2752 eq7474
    | exact resolve eq7474 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq7474
  have eq7485 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3586 eq133
    | exact resolve eq133 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq3586
  have eq7502 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq7485
    | exact resolve eq7485 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7485
  have eq7507 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5880 eq7502
    | exact resolve eq7502 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7502
  have eq7747 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7438 eq938
    | (have j0 := eq938 (σ x) (σ y)
       grind)
    | (have r₁ := eq938 (σ x) (σ y)
       have r₂ := eq7438
       grind)
    | exact resolve eq938 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938 eq7438
  have eq7750 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq7747
  have eq7754 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7750
    | exact resolve eq7750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7750
  have eq7761 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7754
    | exact resolve eq7754 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7754
  have eq7791 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) y) = X0 ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq7507 eq743
    | exact resolve eq743 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq7807 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq758 eq7791
    | exact resolve eq7791 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7791
  have eq7821 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = X0 ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5880 eq7807
    | exact resolve eq7807 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807
  have eq11163 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7761 eq5893
    | exact resolve eq5893 eq7761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5893
  have eq11169 : x ≠ x ∨ (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7761 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq7761
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7761
       grind)
    | exact resolve eq13 eq7761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7761
  have eq11193 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11169
  have eq11196 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11163
  have eq11208 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5883 eq11193
    | exact resolve eq11193 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883 eq11193
  have eq11356 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11208 eq35
    | exact resolve eq35 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11208
  have eq11372 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq11356
    | exact resolve eq11356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11356
  have eq11376 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5896 eq11372
    | exact resolve eq11372 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11372
  have eq12206 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11196 eq37
    | exact resolve eq37 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196
  have eq12231 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12206
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12206
    | exact resolve eq12206 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12206
  have eq12235 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5896 eq12231
    | exact resolve eq12231 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12231
  have eq12244 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12235 eq863
    | exact resolve eq863 eq12235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq12235
  have eq12278 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12244
  have eq12488 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12278 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12278
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12278
       grind)
    | exact resolve eq13 eq12278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12278
  have eq12512 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12488
  have eq12523 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12512
    | exact resolve eq12512 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12512
  have eq12528 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11376 eq12523
    | exact resolve eq12523 eq11376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376 eq12523
  have eq12529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12528
  have eq12532 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12529 eq27
    | exact resolve eq27 eq12529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12529
  have eq12550 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12532
       have r₂ := eq5896
       grind)
    | exact resolve eq12532 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12532
  have eq12555 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12550 eq27
    | exact resolve eq27 eq12550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12585 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5896 eq12555
    | exact resolve eq12555 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896 eq12555
  have eq12589 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq12585
  have eq13296 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4255 eq679
    | exact resolve eq679 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq13323 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6078 eq13296
    | exact resolve eq13296 eq6078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6078 eq13296
  have eq13806 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13323 eq679
    | exact resolve eq679 eq13323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13323
  have eq13856 : x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13806 eq7478
    | exact resolve eq7478 eq13806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7478 eq13806
  have eq13890 : x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13856
  have eq13910 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12550 eq13890
    | exact resolve eq13890 eq12550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13890
  have eq13917 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq912 (M.op x y)
       grind)
    | (have r₁ := eq13910
       have r₂ := eq912 (M.op x y)
       grind)
    | exact resolve eq13910 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912 eq13910
  have eq13936 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13917 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq13917
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13917
       grind)
    | exact resolve eq13 eq13917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13917
  have eq13960 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13936
  have eq17822 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7507 eq7821
    | exact resolve eq7821 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507 eq7821
  have eq17868 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq17822
  have eq17881 : x = y ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq733 eq17868
    | exact resolve eq17868 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17868
  have eq17891 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5880 eq17881
    | exact resolve eq17881 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17881
  have eq17892 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq17891
  have eq17907 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) X1)) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq17892 eq867
    | (have j0 := eq867 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq867 eq17892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17911 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) X1)) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq17907 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17907
  have eq17916 : ∀ X0 : G, (M.op (M.op X0 y) x) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq758 eq17911
    | exact resolve eq17911 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17911
  have eq17920 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5880 eq17916
    | exact resolve eq17916 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17916
  have eq19814 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq733 eq17920
    | exact resolve eq17920 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17920
  have eq19873 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5880 eq19814
    | exact resolve eq19814 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5880 eq19814
  have eq19874 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19873
  have eq19910 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19874 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq19874
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19874
       grind)
    | exact resolve eq13 eq19874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19874
  have eq19934 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19910
  have eq19996 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19934 eq17892
    | exact resolve eq17892 eq19934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17892 eq19934
  have eq20011 : y = (M.op x y) := by grind
  clear eq19996
  have eq20021 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq18
    | exact resolve eq18 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20022 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq24
    | exact resolve eq24 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq20023 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq36
    | exact resolve eq36 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq20024 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq40
    | exact resolve eq40 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq20025 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq181
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq181
    | (have r₁ := eq181
       have r₂ := eq20011
       grind)
    | exact resolve eq181 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq20026 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq733
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq733
    | exact resolve eq733 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq20028 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq834
       have i₂ := eq20011
       grind)
    | exact superpose eq20011 eq834
    | (have r₁ := eq834
       have r₂ := eq20011
       grind)
    | exact resolve eq834 eq20011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq20011
  have eq20032 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq20028
  have eq20033 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq20025
  have eq20036 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20022 eq20
    | exact resolve eq20 eq20022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20055 : ∀ X0 : G, (σ (k X0 (k (M.op x y) x))) = (k (σ X0) (k (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq20022 eq57
    | exact resolve eq57 eq20022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq20022
  have eq20269 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20026 eq13
    | exact resolve eq13 eq20026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20305 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq20269
       have r₂ := eq6010
       grind)
    | exact resolve eq20269 eq6010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6010 eq20269
  have eq20326 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20305 eq37
    | exact resolve eq37 eq20305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq20305
  have eq20340 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq20326
    | exact resolve eq20326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20326
  have eq20344 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20036 eq20340
    | exact resolve eq20340 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20340
  have eq20346 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq20344
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20344
    | exact resolve eq20344 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20344
  have eq20396 : (M.op x y) = (M.op (k (M.op x y) x) x) := by
    first
    | exact superpose eq20033 eq679
    | exact resolve eq679 eq20033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20511 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13960 eq20023
    | exact resolve eq20023 eq13960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13960 eq20023
  have eq20609 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20511
    | exact resolve eq20511 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20511
  have eq20632 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20036 eq20609
    | exact resolve eq20609 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20609
  have eq20642 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20346 eq20632
    | exact resolve eq20632 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20632
  have eq20647 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20036 eq20642
    | exact resolve eq20642 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20642
  have eq20648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20647
  have eq21118 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20648 eq27
    | exact resolve eq27 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20648
  have eq21139 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21118
       have r₂ := eq20036
       grind)
    | exact resolve eq21118 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21118
  have eq21527 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20032 eq20024
    | exact resolve eq20024 eq20032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024 eq20032
  have eq21541 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq21527
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21527
    | exact resolve eq21527 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21527
  have eq21544 : (σ x) = (k (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq20033 eq21541
    | exact resolve eq21541 eq20033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20033 eq21541
  have eq21587 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21544 eq911
    | (have j0 := eq911 (σ y) (σ x)
       grind)
    | (have r₁ := eq911 (σ y) (σ x)
       have r₂ := eq21544
       grind)
    | exact resolve eq911 eq21544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21544
  have eq21588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k (M.op x y) x) := by grind
  clear eq21587
  have eq21592 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq21588
    | exact resolve eq21588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21588
  have eq22803 : (σ (M.op x y)) = (k (σ (k (M.op x y) x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7045 eq20055
    | exact resolve eq20055 eq7045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20055
  have eq22899 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22803
       have i₂ := eq39 sF0
       grind)
    | exact superpose eq39 eq22803
    | exact resolve eq22803 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22803
  have eq22926 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22899
    | exact resolve eq22899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22899
  have eq22947 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20036 eq22926
    | exact resolve eq22926 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22926
  have eq24812 : ∀ X0 : G, (M.op x (M.op x y)) = (k x (M.op x (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq20026 eq4189
    | exact resolve eq4189 eq20026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24865 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq734 eq4189
    | exact resolve eq4189 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq25125 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq764 eq24865
    | exact resolve eq24865 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq24865
  have eq25130 : (M.op x (M.op x y)) = (k x (M.op x x)) := by
    first
    | exact superpose eq758 eq24812
    | exact resolve eq24812 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq24812
  have eq25195 : (M.op x y) = (k x (M.op x x)) := by
    first
    | exact superpose eq20021 eq25130
    | exact resolve eq25130 eq20021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021 eq25130
  have eq25248 : (σ (M.op x y)) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq25195
       grind)
    | exact superpose eq25195 eq35
    | exact resolve eq35 eq25195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq25195
  have eq25255 : (σ (M.op x y)) = (k (σ x) (σ (M.op x x))) := by
    first
    | exact superpose eq20 eq25248
    | exact resolve eq25248 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25248
  have eq25257 : (σ y) = (k (σ x) (σ (M.op x x))) := by
    first
    | exact superpose eq20036 eq25255
    | exact resolve eq25255 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25255
  have eq25272 : (σ x) ≠ (σ y) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | exact superpose eq25257 eq911
    | (have j0 := eq911 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq911 eq25257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq25257
  have eq25274 : (σ x) ≠ (σ y) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | exact superpose eq12589 eq25272
    | exact resolve eq25272 eq12589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25272
  have eq25285 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | exact superpose eq20026 eq25274
    | exact resolve eq25274 eq20026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25274
  have eq25293 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq25285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25285
    | exact resolve eq25285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25285
  have eq25296 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq12589 eq25293
    | exact resolve eq25293 eq12589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25293
  have eq25298 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) := by
    first
    | exact superpose eq20026 eq25296
    | exact resolve eq25296 eq20026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20026 eq25296
  have eq25300 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq25298
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25298
    | exact resolve eq25298 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25298
  have eq25301 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25300
  have eq26436 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21592 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21592
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21592
       grind)
    | exact resolve eq12 eq21592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26443 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    intro X0 X1
    first
    | exact superpose eq21592 eq177
    | exact resolve eq177 eq21592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq26449 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21592 eq679
    | exact resolve eq679 eq21592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq26461 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq21592 eq4189
    | exact resolve eq4189 eq21592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189 eq21592
  have eq26464 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq26436
  have eq26467 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq26 eq26461
    | (have j0 := eq26461 X0
       grind)
    | exact resolve eq26461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26461
  have eq26477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq26464
    | exact resolve eq26464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26464
  have eq26478 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq26477
  have eq26480 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26443 eq26467
    | exact resolve eq26467 eq26443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26443 eq26467
  have eq26482 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq25125 eq26480
    | exact resolve eq26480 eq25125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25125 eq26480
  have eq26695 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26478 eq22947
    | exact resolve eq22947 eq26478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22947 eq26478
  have eq26712 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq20346 eq26695
    | exact resolve eq26695 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20346 eq26695
  have eq26717 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have r₁ := eq26712
       have r₂ := eq12589
       grind)
    | exact resolve eq26712 eq12589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26712
  have eq26721 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq12550 eq26717
    | exact resolve eq26717 eq12550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550 eq26717
  have eq26724 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26721
       have r₂ := eq12589
       grind)
    | exact resolve eq26721 eq12589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12589 eq26721
  have eq26736 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26724 eq7045
    | exact resolve eq7045 eq26724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7045 eq26724
  have eq26784 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq26736
  have eq28000 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21139 eq26482
    | exact resolve eq26482 eq21139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26482
  have eq28045 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) := by grind
  clear eq28000
  have eq28059 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) := by
    first
    | (have r₁ := eq28045
       have r₂ := eq25301
       grind)
    | exact resolve eq28045 eq25301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28045
  have eq28085 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq28059 eq26449
    | exact resolve eq26449 eq28059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26449 eq28059
  have eq28122 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq28085
  have eq28144 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21139 eq28122
    | exact resolve eq28122 eq21139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28122
  have eq28145 : x = (k (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq28144
  have eq28186 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28145 eq20396
    | exact resolve eq20396 eq28145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20396 eq28145
  have eq28262 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq28186
       grind)
    | exact superpose eq28186 eq13
    | exact resolve eq13 eq28186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28186
  have eq28305 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28262
       have r₂ := eq26784
       grind)
    | exact resolve eq28262 eq26784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26784 eq28262
  have eq28475 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq28305
       grind)
    | exact superpose eq28305 eq39
    | exact resolve eq39 eq28305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq28305
  have eq28496 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28475
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28475
    | exact resolve eq28475 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28475
  have eq28503 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq28496
    | exact resolve eq28496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28496
  have eq28506 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20036 eq28503
    | exact resolve eq28503 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28503
  have eq28605 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq28506 eq867
    | (have j0 := eq867 (σ x) (σ x) x x
       grind)
    | exact resolve eq867 eq28506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq28609 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq28605 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28605
  have eq28615 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have j0 := eq28609 X0 X1
       grind)
    | (have r₁ := eq28609 X0 X1
       have r₂ := eq25301
       grind)
    | exact resolve eq28609 eq25301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28609
  have eq28620 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq194 eq28615
    | (have j0 := eq28615 X0 (σ y)
       grind)
    | exact resolve eq28615 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq28615
  have eq29719 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq28620
    | (have j0 := eq28620 (σ x)
       grind)
    | exact resolve eq28620 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28620
  have eq29793 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21139 eq29719
    | exact resolve eq29719 eq21139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21139 eq29719
  have eq29843 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq29793
  have eq29859 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq29843
       have r₂ := eq25301
       grind)
    | exact resolve eq29843 eq25301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25301 eq29843
  have eq29898 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq29859 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq29859
       grind)
    | exact resolve eq13 eq29859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29924 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq29898
  have eq29984 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29924 eq28506
    | exact resolve eq28506 eq29924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28506 eq29924
  have eq30001 : (σ x) = (σ y) := by grind
  clear eq29984
  have eq30011 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30001 eq26
    | exact resolve eq26 eq30001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30186 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29859 eq30011
    | exact resolve eq30011 eq29859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29859 eq30011
  have eq30371 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq30186 eq27
    | exact resolve eq27 eq30186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30186
  have eq30403 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq20036 eq30371
    | exact resolve eq30371 eq20036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20036 eq30371
  have eq30406 : False := by grind
  exact eq30406

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq30 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | (have j0 := eq29 X0
       grind)
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq155 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43 y x
       grind)
    | exact superpose eq43 eq16
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq387 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq42
    | (have j1 := eq30 X0
       grind)
    | exact resolve eq42 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq42
  have eq400 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq390
    | (have j0 := eq390 X0
       grind)
    | exact resolve eq390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq401 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq496 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq61
  have eq699 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq155
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq155
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq155
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq155 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq700 : x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq699
  have eq1022 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq400
  have eq1042 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1022 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq3319 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq496 (σ X0)
       grind)
    | exact superpose eq496 eq38
    | exact resolve eq38 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq496
  have eq5245 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq1042 X0
       grind)
    | exact superpose eq1042 eq10
    | (have j1 := eq1042 X0
       grind)
    | exact resolve eq10 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq5717 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq700
       grind)
    | exact superpose eq700 eq16
    | exact resolve eq16 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq5930 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5245 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5245
    | (have j0 := eq5245 (σ X0)
       grind)
    | exact resolve eq5245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245
  have eq5994 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5930 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq5930
    | (have j0 := eq5930 X0
       grind)
    | exact resolve eq5930 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq5999 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5994 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5994
    | (have j0 := eq5994 X0
       grind)
    | exact resolve eq5994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994
  have eq7120 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3319 X0
       have i₂ := eq5999 X0
       grind)
    | exact superpose eq5999 eq3319
    | (have j1 := eq5999 X0
       grind)
    | exact resolve eq3319 eq5999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319 eq5999
  have eq7157 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7120 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7120
    | (have j0 := eq7120 X0
       grind)
    | exact resolve eq7120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7120
  have eq7254 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7157 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq7157
    | exact resolve eq7157 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq7157
  have eq226545 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq226556 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq226545 X0
       have j1 := eq7254 X0
       grind)
    | (have r₁ := eq226545 X0
       have r₂ := eq7254 X0
       grind)
    | exact resolve eq226545 eq7254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7254 eq226545
  have eq226623 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq226556 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226556
    | exact resolve eq226556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226556
  have eq226959 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq226623 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq226623
    | exact resolve eq226623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq226623
  have eq227005 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq226959 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226959
    | exact resolve eq226959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226959
  have eq228426 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq227005 (σ X0)
       grind)
    | exact superpose eq227005 eq15
    | exact resolve eq15 eq227005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228718 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq228426 X0
       have i₂ := eq227005 X0
       grind)
    | exact superpose eq227005 eq228426
    | exact resolve eq228426 eq227005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228426
  have eq231013 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0)
       have i₂ := eq228718 X0
       grind)
    | exact superpose eq228718 eq22
    | exact resolve eq22 eq228718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602657 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq5717
       have r₂ := eq228718 x
       grind)
    | exact resolve eq5717 eq228718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5717
  have eq602658 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq602657
       have i₂ := eq228718 x
       grind)
    | exact superpose eq228718 eq602657
    | exact resolve eq602657 eq228718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602657
  have eq602689 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq401 x
       have i₂ := eq602658
       grind)
    | exact superpose eq602658 eq401
    | exact resolve eq401 eq602658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq602658
  have eq603071 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq602689
       have i₂ := eq227005 x
       grind)
    | exact superpose eq227005 eq602689
    | exact resolve eq602689 eq227005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227005 eq602689
  have eq603072 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq603071
  have eq603118 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq603072
       grind)
    | exact superpose eq603072 eq16
    | exact resolve eq16 eq603072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603072
  have eq603119 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq603118
       have r₂ := eq228718 x
       grind)
    | exact resolve eq603118 eq228718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603118
  have eq603121 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq603119
       grind)
    | exact superpose eq603119 eq10
    | exact resolve eq10 eq603119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603119
  have eq604053 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq603121
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq603121
    | exact resolve eq603121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603121
  have eq604558 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq604053
       grind)
    | exact superpose eq604053 eq16
    | exact resolve eq16 eq604053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604053
  have eq604559 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq604558
       have r₂ := eq228718 x
       grind)
    | exact resolve eq604558 eq228718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228718 eq604558
  have eq604598 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq231013 x
       have i₂ := eq604559
       grind)
    | exact superpose eq604559 eq231013
    | exact resolve eq231013 eq604559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231013
  have eq604620 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq604559
       grind)
    | exact superpose eq604559 eq10
    | exact resolve eq10 eq604559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604559
  have eq605597 : y = (M.op x x) := by
    first
    | (have i₁ := eq604620
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq604620
    | exact resolve eq604620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604620
  have eq606266 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 x
       have i₂ := eq605597
       grind)
    | exact superpose eq605597 eq22
    | exact resolve eq22 eq605597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq605597
  have eq639854 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq604598
       grind)
    | exact superpose eq604598 eq16
    | exact resolve eq16 eq604598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604598
  have eq640197 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq639854
       have i₂ := eq606266
       grind)
    | exact superpose eq606266 eq639854
    | exact resolve eq639854 eq606266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606266 eq639854
  have eq640198 : False := by grind
  exact eq640198

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq75 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq144 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 y x
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 y x
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq160 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq26
    | exact resolve eq26 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ (M.op X0 X0))
       have i₂ := eq160 X0
       grind)
    | exact superpose eq160 eq9
    | exact resolve eq9 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq313 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq312
    | exact resolve eq312 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq312
  have eq326 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq313 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq313
    | exact resolve eq313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq331 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq326
    | exact resolve eq326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq334 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq331
    | exact resolve eq331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq382 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq334 X0 X0
       grind)
    | exact superpose eq334 eq9
    | exact resolve eq9 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op X0 X0)
       have i₂ := eq334 X0 X0
       grind)
    | exact superpose eq334 eq26
    | exact resolve eq26 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq384 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq384
    | exact resolve eq384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq144
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq144
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq144
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq144
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq144 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq779 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq778
  have eq787 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1 (M.op X0 X0)
       have i₂ := eq334 X0 X0
       grind)
    | exact superpose eq334 eq382
    | exact resolve eq382 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq382 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq25 X1 X1 X0 X2
       grind)
    | exact superpose eq25 eq382
    | exact resolve eq382 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq382
  have eq1359 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq788 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq788
    | exact resolve eq788 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1405 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1359 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq334 X0 X1
       grind)
    | exact superpose eq334 eq1359
    | exact resolve eq1359 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1883 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X0 X1 X2
       have i₂ := eq1405 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq1405 eq105
    | exact resolve eq105 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq2029 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1883 X0 X1 (M.op X0 X0)
       have i₂ := eq334 X0 X0
       grind)
    | exact superpose eq334 eq1883
    | exact resolve eq1883 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq1883
  have eq2171 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq788 X3 X1 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq2029 X1 X0
       grind)
    | exact superpose eq2029 eq788
    | exact resolve eq788 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq2029
  have eq3584 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110 X0 X1 X2 X3 X4 X5
       have i₂ := eq1405 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq1405 eq110
    | exact resolve eq110 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq3925 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3584 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq26 (M.op X1 X2)
       grind)
    | exact superpose eq26 eq3584
    | exact resolve eq3584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3584
  have eq4011 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3925 X0 X1 X2 X3
       have i₂ := eq787 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq787 eq3925
    | exact resolve eq3925 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq4038 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4011 X0 X1 X2 X3
       have i₂ := eq1405 X1 X0
       grind)
    | exact superpose eq1405 eq4011
    | exact resolve eq4011 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405 eq4011
  have eq7290 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4038 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq4038
    | exact resolve eq4038 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038
  have eq7565 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7290 X0 X1 X2 X3 X4
       have i₂ := eq787 X0 X0
       grind)
    | exact superpose eq787 eq7290
    | exact resolve eq7290 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7290
  have eq13975 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq779
       grind)
    | exact superpose eq779 eq16
    | exact resolve eq16 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq13976 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq13975
       have r₂ := eq23 x
       grind)
    | exact resolve eq13975 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13975
  have eq119103 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 (M.op X1 (M.op X2 x))) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7565 y X1 y x x
       have i₂ := eq13976
       grind)
    | exact superpose eq13976 eq7565
    | exact resolve eq7565 eq13976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565 eq13976
  have eq119137 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq119103 x x x
       have i₂ := eq2171 x x x x
       grind)
    | exact superpose eq2171 eq119103
    | exact resolve eq119103 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq119103
  have eq213628 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq75 x x
       have i₂ := eq119137
       grind)
    | exact superpose eq119137 eq75
    | exact resolve eq75 eq119137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq119137
  have eq213989 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq213628 x
       have i₂ := eq787 (σ y) x
       grind)
    | exact superpose eq787 eq213628
    | exact resolve eq213628 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq213628
  have eq213991 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq213989
       have i₂ := eq23 y
       grind)
    | exact superpose eq23 eq213989
    | exact resolve eq213989 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213989
  have eq213992 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq213991
  have eq214876 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq213992
       grind)
    | exact superpose eq213992 eq10
    | exact resolve eq10 eq213992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213992
  have eq215227 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq214876
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq214876
    | exact resolve eq214876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214876
  have eq215230 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq215227
       grind)
    | exact superpose eq215227 eq16
    | exact resolve eq16 eq215227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215227
  have eq215231 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq215230
       have r₂ := eq23 x
       grind)
    | exact resolve eq215230 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq215230
  have eq216294 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq399 y
       have i₂ := eq215231
       grind)
    | exact superpose eq215231 eq399
    | exact resolve eq399 eq215231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq216358 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq215231
       grind)
    | exact superpose eq215231 eq10
    | exact resolve eq10 eq215231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215231
  have eq216804 : x = (M.op y y) := by
    first
    | (have i₁ := eq216358
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq216358
    | exact resolve eq216358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216358
  have eq216970 : x = (M.op x y) := by
    first
    | (have i₁ := eq384 y
       have i₂ := eq216804
       grind)
    | exact superpose eq216804 eq384
    | exact resolve eq384 eq216804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq216804
  have eq265186 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq216294
       grind)
    | exact superpose eq216294 eq16
    | exact resolve eq16 eq216294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216294
  have eq265519 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq265186
       have i₂ := eq216970
       grind)
    | exact superpose eq216970 eq265186
    | exact resolve eq265186 eq216970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216970 eq265186
  have eq265520 : False := by grind
  exact eq265520

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq37 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq96 X0 X0
       have r₂ := eq54 X0 X0
       grind)
    | exact resolve eq96 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq96
  have eq313 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq313
    | exact resolve eq313 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq313
  have eq320 : False := by grind
  exact eq320

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation1924 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq457 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq606 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | (have j1 := eq480 x y
       grind)
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq3482 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq454
    | exact resolve eq454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq3536 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3482 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3482
    | (have j0 := eq3482 X0 X1
       grind)
    | exact resolve eq3482 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3482
  have eq7298 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq606
       have i₂ := eq3536 y x
       grind)
    | exact superpose eq3536 eq606
    | (have j1 := eq3536 y x
       grind)
    | (have r₁ := eq606
       have r₂ := eq3536 y x
       grind)
    | (have r₁ := eq606
       have r₂ := eq3536 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq606
       have r₂ := eq3536 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq606 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq3536
  have eq7299 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7298
  have eq15925 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7299
       grind)
    | exact superpose eq7299 eq16
    | exact resolve eq16 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299
  have eq15926 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15925
       have r₂ := eq22 x
       grind)
    | exact resolve eq15925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15925
  have eq15927 : y = (M.op (M.op x (M.op x x)) (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq15926
       grind)
    | exact superpose eq15926 eq9
    | exact resolve eq9 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15926
  have eq15935 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15927
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq15927
    | exact resolve eq15927 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15927
  have eq15936 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15935
       grind)
    | exact superpose eq15935 eq16
    | exact resolve eq16 eq15935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15935
  have eq15937 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15936
       have r₂ := eq22 x
       grind)
    | exact resolve eq15936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15936
  have eq15942 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (σ (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq15937
       grind)
    | exact superpose eq15937 eq9
    | exact resolve eq9 eq15937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15937
  have eq15955 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15942
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq15942
    | exact resolve eq15942 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq15942
  have eq15956 : (σ x) = (σ y) := by grind
  clear eq15955
  have eq15959 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15956
       grind)
    | exact superpose eq15956 eq16
    | exact resolve eq16 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15960 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15956
       grind)
    | exact superpose eq15956 eq10
    | exact resolve eq10 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15956
  have eq16127 : x = y := by
    first
    | (have i₁ := eq15960
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15960
    | exact resolve eq15960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15960
  have eq16128 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15959
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq15959
    | exact resolve eq15959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15959
  have eq16129 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16128
       have i₂ := eq16127
       grind)
    | exact superpose eq16127 eq16128
    | exact resolve eq16128 eq16127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16127 eq16128
  have eq16130 : False := by grind
  exact eq16130

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq123 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X0 X3 (M.op X0 X0)
       have i₂ := eq20 X0 X1 X2
       grind)
    | (have i₁ := eq22 X1 X1 (M.op X1 X2)
       have i₂ := eq20 X1 X1 X2
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq167 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq45
  have eq194 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq281 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    grind
  clear eq34
  have eq300 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq281 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq1728 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq3218 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1 X0 x (M.op X1 X0)
       have i₂ := eq300 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq300 eq123
    | (have j1 := eq300 X1 X0 x x
       grind)
    | exact resolve eq123 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq300
  have eq3283 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3218 X0 X1
       have j1 := eq1728 X1 X0
       grind)
    | (have r₁ := eq3218 X0 X1
       have r₂ := eq1728 X0 X1
       grind)
    | (have r₁ := eq3218 X1 X0
       have r₂ := eq1728 X0 X1
       grind)
    | exact resolve eq3218 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728 eq3218
  have eq186974 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3283 (σ X1) (σ X0)
       grind)
    | exact superpose eq3283 eq15
    | exact resolve eq15 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186993 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186974 X0 X1
       have i₂ := eq3283 X1 X0
       grind)
    | exact superpose eq3283 eq186974
    | exact resolve eq186974 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283 eq186974
  have eq187020 : False := by grind
  exact eq187020

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq9 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X1 X1) X2)) X1) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X1) X2) (M.op X2 x)
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  clear eq23
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq74 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = (M.op (M.op X1 X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30 X1 X4 X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq30 X2 X1 X2
       have i₂ := eq30 X2 X2 X2
       grind)
    | exact superpose eq30 eq30
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 X1) X4 X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq30 X2 X2 X2
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq189 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X3 X2)) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq225 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq251 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X1 X2) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq60 X1 X2 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq364 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X5 X5) (M.op X4 X0)) (M.op (M.op X4 X1) (M.op X1 X3))) = X5 := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq9 X5 (M.op X4 X0) (M.op X0 x)
       have i₂ := eq74 x X4 X0 X3 X1
       grind)
    | (have i₁ := eq9 X5 (M.op X4 X0) (M.op X0 x)
       have i₂ := eq74 X3 X4 X1 x X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq637 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq225
  have eq742 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq824 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq742 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq850 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq824 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq857 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq850 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq850
    | exact resolve eq850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq850 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq850
    | exact resolve eq850 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq863 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq858 X0
       have i₂ := eq850 X0
       grind)
    | exact superpose eq850 eq858
    | exact resolve eq858 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq864 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq857 X0
       have i₂ := eq850 X0
       grind)
    | exact superpose eq850 eq857
    | exact resolve eq857 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq857
  have eq882 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (M.op (M.op X2 X2) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X2 X1 (τ X0)
       have i₂ := eq863 X0
       grind)
    | exact superpose eq863 eq32
    | exact resolve eq32 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq863
  have eq1032 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (k X0 X3) ∨ (M.op (M.op (M.op X0 X3) X1) (M.op X1 X2)) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    grind
  clear eq189
  have eq1075 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X1) (M.op X1 X2)) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1032 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq8860 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X3) X2) X4)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq94 X3 X0 X1 X4 (M.op (M.op X1 X3) X2)
       have i₂ := eq1075 X0 (M.op X1 X3) X2 X1
       grind)
    | exact superpose eq1075 eq94
    | (have j1 := eq1075 X0 X1 X2 X1
       grind)
    | exact resolve eq94 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1075
  have eq8981 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8860 X0 X1 x x x
       have i₂ := eq251 x X1 x x
       grind)
    | exact superpose eq251 eq8860
    | (have j0 := eq8860 X0 X1 x x x
       grind)
    | exact resolve eq8860 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq8860
  have eq9629 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X3 X4)) (M.op (M.op X3 X5) (M.op X5 X2))) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq364 X4 X5 X2 X3 X1
       have i₂ := eq8981 X0 X1
       grind)
    | (have i₁ := eq364 X0 X1 X3 X4 X0
       have i₂ := eq8981 X0 X1
       grind)
    | exact superpose eq8981 eq364
    | (have j1 := eq8981 X0 X1
       grind)
    | exact resolve eq364 eq8981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9636 : ∀ X0 X1 X2 X3 : G, (τ X1) = (M.op (M.op (τ (M.op X0 X0)) (M.op (M.op X2 X2) X3)) X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq882 X1 X3 X2
       have i₂ := eq8981 X0 X1
       grind)
    | (have i₁ := eq882 X0 X1 X2
       have i₂ := eq8981 X0 X1
       grind)
    | exact superpose eq8981 eq882
    | (have j1 := eq8981 X0 X1
       grind)
    | exact resolve eq882 eq8981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8981
  have eq9788 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9636 X0 X1 x x
       have i₂ := eq882 X0 x x
       grind)
    | exact superpose eq882 eq9636
    | (have j0 := eq9636 X0 X1 x x
       grind)
    | exact resolve eq9636 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq9636
  have eq9791 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9629 X0 X1 x x x x
       have i₂ := eq364 x x x x X0
       grind)
    | (have i₁ := eq9629 X0 X1 x x x x
       have i₂ := eq364 X0 X1 x x (M.op (M.op (M.op X0 X0) (M.op x x)) (M.op (M.op x x) (M.op x x)))
       grind)
    | exact superpose eq364 eq9629
    | (have j0 := eq9629 X0 X1 x x x x
       grind)
    | exact resolve eq9629 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq9629
  have eq11907 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9788 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9788
    | (have j0 := eq9788 (σ X0) (σ X1)
       grind)
    | exact resolve eq9788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9788
  have eq11947 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11907 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11907
    | (have j0 := eq11907 X0 X1
       grind)
    | exact resolve eq11907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11907
  have eq11952 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11947 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11947
    | (have j0 := eq11947 X0 X1
       grind)
    | exact resolve eq11947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11947
  have eq12698 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq11952 y x
       grind)
    | exact superpose eq11952 eq16
    | (have j1 := eq11952 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq11952 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq11952 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq11952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11952
  have eq12785 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq12698
       have i₂ := eq9791 y x
       grind)
    | exact superpose eq9791 eq12698
    | (have j1 := eq9791 x y
       grind)
    | (have r₁ := eq12698
       have r₂ := eq9791 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12698
       have r₂ := eq9791 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12698 eq9791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9791 eq12698
  have eq12786 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq12785
  have eq12787 : x = y := by grind
  clear eq12786
  have eq12796 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12787
       grind)
    | exact superpose eq12787 eq16
    | exact resolve eq16 eq12787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12787
  have eq12797 : False := by grind
  exact eq12797
