import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X3) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq62 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (k X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 X2 X0 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq71
    | exact resolve eq71 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq130 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq62
    | exact resolve eq62 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq629 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (k X3 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X0 X1 X2 X3
       have i₂ := eq130 X3 X3 (M.op X2 X2)
       grind)
    | exact superpose eq130 eq64
    | exact resolve eq64 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq630 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (k X3 X3) (k X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq629 X0 X1 X2 X3
       have i₂ := eq123 X2
       grind)
    | exact superpose eq123 eq629
    | exact resolve eq629 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq631 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (k X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 X0 X1 X2 X3
       have i₂ := eq130 X0 X0 X1
       grind)
    | exact superpose eq130 eq65
    | exact resolve eq65 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq632 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (k X0 X0) X1) X2) = (M.op (k X2 X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq631 X0 X1 X2 X3
       have i₂ := eq130 X2 X2 (M.op X1 X3)
       grind)
    | exact superpose eq130 eq631
    | exact resolve eq631 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq633 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) X2) = (M.op (k X2 X2) (k X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq630 X0 X0 X1 X2
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq630
    | exact resolve eq630 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 X2 : G, (k (k X2 X2) (k X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 (k X2 X2)
       have i₂ := eq630 X0 X1 X2 X2
       grind)
    | exact superpose eq630 eq123
    | exact resolve eq123 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq722 : ∀ X0 X1 X2 : G, (k (k X2 X2) (k X2 X2)) = (M.op (k X2 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq719 X0 X1 X2
       have i₂ := eq128 X2 (M.op X0 X1) X2
       grind)
    | exact superpose eq128 eq719
    | exact resolve eq719 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1270 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (M.op (k X0 X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (k X1 X1)
       have i₂ := eq633 X0 X1 X1
       grind)
    | exact superpose eq633 eq123
    | exact resolve eq123 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq1273 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (k X1 X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1270 X0 X1
       have i₂ := eq128 X1 (k X0 X0) X1
       grind)
    | exact superpose eq128 eq1270
    | exact resolve eq1270 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1270
  have eq1659 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) X2) = (k (k X2 X2) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq722 X1 x X2
       have i₂ := eq632 X0 X1 X2 x
       grind)
    | exact superpose eq632 eq722
    | exact resolve eq722 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq722
  have eq8946 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8947 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8946 X0 X1
       have i₂ := eq123 X1
       grind)
    | exact superpose eq123 eq8946
    | (have j0 := eq8946 X0 X1
       grind)
    | exact resolve eq8946 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq8946
  have eq9143 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8947 (σ y) (σ x)
       grind)
    | exact superpose eq8947 eq16
    | (have j1 := eq8947 x (σ x)
       grind)
    | exact resolve eq16 eq8947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9190 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9143
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9143
    | exact resolve eq9143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9143
  have eq9197 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq9190
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq9190
    | exact resolve eq9190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9190
  have eq16362 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq9197
       have i₂ := eq8947 y x
       grind)
    | exact superpose eq8947 eq9197
    | (have j1 := eq8947 x x
       grind)
    | exact resolve eq9197 eq8947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8947 eq9197
  have eq16363 : (σ x) = (σ (k x x)) ∨ x = (k x x) := by grind
  clear eq16362
  have eq16365 : (k x x) = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq16363
       grind)
    | exact superpose eq16363 eq10
    | exact resolve eq10 eq16363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16363
  have eq16403 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16365
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16365
    | exact resolve eq16365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16365
  have eq16404 : x = (k x x) := by grind
  clear eq16403
  have eq16429 : ∀ X0 : G, (k x x) = (M.op x (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1273 X0 x
       have i₂ := eq16404
       grind)
    | exact superpose eq16404 eq1273
    | exact resolve eq1273 eq16404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq16438 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1659 x X0 X1
       have i₂ := eq16404
       grind)
    | exact superpose eq16404 eq1659
    | exact resolve eq1659 eq16404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq16462 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (k x x) X1) := by
    intro X1
    first
    | (have i₁ := eq16438 x X1
       have i₂ := eq130 x x X1
       grind)
    | exact superpose eq130 eq16438
    | exact resolve eq16438 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq16438
  have eq16466 : ∀ X0 : G, x = (M.op x (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16429 X0
       have i₂ := eq16404
       grind)
    | exact superpose eq16404 eq16429
    | exact resolve eq16429 eq16404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429
  have eq16487 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq16462 X1
       have i₂ := eq16404
       grind)
    | exact superpose eq16404 eq16462
    | exact resolve eq16462 eq16404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16404 eq16462
  have eq16590 : ∀ X0 : G, x = (M.op x (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16466 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq16466
    | exact resolve eq16466 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21181 : ∀ X0 : G, (k (σ (k X0 X0)) (σ (k X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16487 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq16487
    | exact resolve eq16487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21182 : ∀ X0 : G, (k (τ (k X0 X0)) (τ (k X0 X0))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16487 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq16487
    | exact resolve eq16487 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21332 : ∀ X0 : G, (τ (k (k X0 X0) (k X0 X0))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21182 X0
       have i₂ := eq31 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq31 eq21182
    | exact resolve eq21182 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21182
  have eq21333 : ∀ X0 : G, (σ (k (k X0 X0) (k X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21181 X0
       have i₂ := eq15 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq15 eq21181
    | exact resolve eq21181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21181
  have eq21370 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq21332 X0
       have i₂ := eq16487 X0
       grind)
    | exact superpose eq16487 eq21332
    | exact resolve eq21332 eq16487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21332
  have eq21371 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq21333 X0
       have i₂ := eq16487 X0
       grind)
    | exact superpose eq16487 eq21333
    | exact resolve eq21333 eq16487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16487 eq21333
  have eq22177 : ∀ X0 : G, (τ x) = (M.op x (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21370 (k X0 X0)
       have i₂ := eq16466 X0
       grind)
    | exact superpose eq16466 eq21370
    | exact resolve eq21370 eq16466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16466 eq21370
  have eq22194 : x = (τ x) := by
    first
    | (have i₁ := eq22177 x
       have i₂ := eq16590 x
       grind)
    | exact superpose eq16590 eq22177
    | exact resolve eq22177 eq16590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16590 eq22177
  have eq22236 : x = (σ x) := by
    first
    | (have i₁ := eq11 x
       have i₂ := eq22194
       grind)
    | exact superpose eq22194 eq11
    | exact resolve eq11 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22194
  have eq22253 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22236
       grind)
    | exact superpose eq22236 eq16
    | exact resolve eq16 eq22236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22236
  have eq23891 : False := by grind
  exact eq23891

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq29 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq150 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq29 (τ X0)
       grind)
    | exact superpose eq29 eq19
    | (have j1 := eq29 (τ X0)
       grind)
    | exact resolve eq19 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29
  have eq154 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq150
    | (have j0 := eq150 X0
       grind)
    | exact resolve eq150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq158 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq154
    | (have j0 := eq154 X0
       grind)
    | exact resolve eq154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq162 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq158 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq158 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq158 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq167 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq162 (σ X0)
       grind)
    | exact superpose eq162 eq15
    | exact resolve eq15 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq162 X0
       grind)
    | exact superpose eq162 eq188
    | exact resolve eq188 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq188
  have eq722 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41
    | exact resolve eq41 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq735 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq1939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq167 x y
       grind)
    | exact superpose eq167 eq16
    | (have j1 := eq167 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq167 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq167 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq167 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq1964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1939
  have eq2005 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1964
       grind)
    | exact superpose eq1964 eq16
    | exact resolve eq16 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2006 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1964
       grind)
    | exact superpose eq1964 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1964
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1964
       grind)
    | exact resolve eq12 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2021 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq2006
  have eq2024 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2021
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2021
    | exact resolve eq2021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq5613 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq735 x y
       have i₂ := eq2024
       grind)
    | exact superpose eq2024 eq735
    | (have j0 := eq735 x y
       grind)
    | exact resolve eq735 eq2024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq2024
  have eq5640 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq5613
  have eq5656 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5640
       have r₂ := eq2005
       grind)
    | exact resolve eq5640 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq5640
  have eq7180 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5656
       grind)
    | exact superpose eq5656 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq5656
       grind)
    | exact resolve eq12 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7209 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7180
  have eq9030 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq31 x y
       have i₂ := eq7209
       grind)
    | exact superpose eq7209 eq31
    | (have j0 := eq31 x y
       grind)
    | exact resolve eq31 eq7209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7209
  have eq9033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9030
  have eq12134 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq9033
       grind)
    | exact superpose eq9033 eq16
    | exact resolve eq16 eq9033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9033
  have eq15486 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12134
       have i₂ := eq5656
       grind)
    | exact superpose eq5656 eq12134
    | exact resolve eq12134 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656 eq12134
  have eq15487 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15486
  have eq15488 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq15487
  have eq18998 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15488
       grind)
    | exact superpose eq15488 eq10
    | exact resolve eq10 eq15488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15488
  have eq19105 : x = y ∨ x = y := by
    first
    | (have i₁ := eq18998
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18998
    | exact resolve eq18998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18998
  have eq19106 : x = y := by grind
  clear eq19105
  have eq22333 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19106
       grind)
    | exact superpose eq19106 eq16
    | exact resolve eq16 eq19106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19106
  have eq22334 : False := by grind
  exact eq22334

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq77 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (M.op X2 X2) ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X0) X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq114 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq106 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq106 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq106 X1 X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | exact resolve eq106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq128 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 X2) ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq77 X2 X1 X2
       have j1 := eq84 X2 X1 X2
       grind)
    | (have r₁ := eq77 X0 X1 X2
       have r₂ := eq84 X0 X1 X2
       grind)
    | (have r₁ := eq77 X2 X1 X0
       have r₂ := eq84 X0 X1 X2
       grind)
    | (have r₁ := eq77 X0 X1 X2
       have r₂ := eq84 (M.op X1 X2) X1 (M.op X2 X2)
       grind)
    | exact resolve eq77 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq84
  have eq406 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq410 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq406 X0 X1
       have j1 := eq128 X0 X1 X0
       grind)
    | (have r₁ := eq406 x x
       have r₂ := eq128 X0 x x
       grind)
    | (have r₁ := eq406 x X1
       have r₂ := eq128 X0 X1 x
       grind)
    | (have r₁ := eq406 X0 X1
       have r₂ := eq128 X0 X1 x
       grind)
    | exact resolve eq406 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq406
  have eq451 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq410 (σ X1) (σ X0)
       grind)
    | exact superpose eq410 eq15
    | exact resolve eq15 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq410 X1 X0
       grind)
    | exact superpose eq410 eq451
    | exact resolve eq451 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq451
  have eq1101 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq458 x y
       grind)
    | exact superpose eq458 eq16
    | (have r₁ := eq16
       have r₂ := eq458 x y
       grind)
    | exact resolve eq16 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq1127 : False := by grind
  exact eq1127

/-- `Equation4646`: `(x ◇ y) ◇ x = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pyx_Equation4646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X1) := by
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
  clear eq25
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
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | (have i₁ := eq14 (M.op X2 X1) X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq14 (M.op X0 X1) X0 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op x y) y) := by
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
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X3 X1)
       have i₂ := eq14 X3 X1 X0
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X2 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X1 x
       grind)
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq14 X0 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq37
  have eq91 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq91
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq217 : (M.op (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq51 (M.op x y)
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq217 eq14
    | exact resolve eq14 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq244 x
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq244
    | exact resolve eq244 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq244
  have eq251 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq217 eq57
    | exact resolve eq57 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1125 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 y X1 X0
       have i₂ := eq251 (M.op X1 y)
       grind)
    | exact superpose eq251 eq53
    | exact resolve eq53 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq251
  have eq1237 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq52 eq1125
    | exact resolve eq1125 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1320 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 X1 X2 x
       have i₂ := eq1125 x X1
       grind)
    | exact superpose eq1125 eq54
    | exact resolve eq54 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1402 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1320 X1 x X1
       have i₂ := eq62 (M.op X1 x) X1 X0
       grind)
    | (have i₁ := eq1320 X1 x X1
       have i₂ := eq62 X0 X1 (M.op X1 x)
       grind)
    | exact superpose eq62 eq1320
    | exact resolve eq1320 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1320
  have eq7173 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq7199 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq7173
    | exact resolve eq7173 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7173
  have eq7202 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq7199
       have r₂ := eq13 x x
       grind)
    | exact resolve eq7199 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq7203 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq44
    | exact resolve eq44 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq7677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq7678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7677
    | exact resolve eq7677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7677
  have eq7689 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7678
       have r₂ := eq28
       grind)
    | exact resolve eq7678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7678
  have eq7691 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7689
    | exact resolve eq7689 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7689
  have eq7697 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7691 eq121
    | exact resolve eq121 eq7691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7691
  have eq7751 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7697 eq104
    | exact resolve eq104 eq7697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq7697
  have eq7770 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq7751
    | exact resolve eq7751 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7751
  have eq8675 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq7770
       grind)
    | exact superpose eq7770 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq7770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7770
  have eq8676 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8675
  have eq8678 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8676
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8676
    | exact resolve eq8676 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8676
  have eq8679 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8678
  have eq8694 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121 y
       have i₂ := eq8679
       grind)
    | exact superpose eq8679 eq121
    | exact resolve eq121 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8702 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 y y X0 X1
       have i₂ := eq8679
       grind)
    | exact superpose eq8679 eq59
    | exact resolve eq59 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8709 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1402 y y
       have i₂ := eq8679
       grind)
    | exact superpose eq8679 eq1402
    | exact resolve eq1402 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8679
  have eq8710 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8709
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8709
    | exact resolve eq8709 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8709
  have eq8716 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8702 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8702
    | (have j0 := eq8702 X0 X1
       grind)
    | exact resolve eq8702 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8702
  have eq8727 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq8716 x X1
       have i₂ := eq1402 x X1
       grind)
    | (have i₁ := eq8716 x y
       have i₂ := eq1402 x X1
       grind)
    | exact superpose eq1402 eq8716
    | exact resolve eq8716 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8716
  have eq8735 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq8694
       grind)
    | exact superpose eq8694 eq82
    | exact resolve eq82 eq8694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq8694
  have eq8751 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8735
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8735
    | exact resolve eq8735 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8735
  have eq8759 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8710 eq245
    | exact resolve eq245 eq8710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq8710
  have eq8829 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8751 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8751
  have eq8830 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8829
  have eq8834 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8830
    | exact resolve eq8830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8830
  have eq8835 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8834
  have eq8849 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8759 eq121
    | exact resolve eq121 eq8759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8759
  have eq8966 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8835 eq1402
    | exact resolve eq1402 eq8835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8835
  have eq8969 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq8966
    | exact resolve eq8966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8966
  have eq9005 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8849 eq140
    | exact resolve eq140 eq8849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq8849
  have eq9021 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq9005
    | exact resolve eq9005 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9005
  have eq9125 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9021 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq9021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9021
  have eq9126 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9125
  have eq9267 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9126 eq1125
    | exact resolve eq1125 eq9126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9617 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8727 eq8969
    | exact resolve eq8969 eq8727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8727 eq8969
  have eq9674 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9617
  have eq11182 : (σ (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9267 eq9126
    | exact resolve eq9126 eq9267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9126 eq9267
  have eq11205 : (σ (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11182
  have eq11261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11205 eq9674
    | exact resolve eq9674 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9674 eq11205
  have eq11285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11261
  have eq11320 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11285
       have r₂ := eq28
       grind)
    | exact resolve eq11285 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11285
  have eq11332 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11320 eq229
    | exact resolve eq229 eq11320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq11336 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11320 eq1237
    | exact resolve eq1237 eq11320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq11355 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11332
    | exact resolve eq11332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332
  have eq11364 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11355 eq121
    | exact resolve eq121 eq11355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq11405 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11320 eq11364
    | exact resolve eq11364 eq11320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11320 eq11364
  have eq11424 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11405
  have eq11525 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11424 eq50
    | exact resolve eq50 eq11424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11424
  have eq11556 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11525
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq11525
    | exact resolve eq11525 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202 eq11525
  have eq11565 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11556
    | exact resolve eq11556 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11556
  have eq11635 : (M.op (M.op x y) x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1125 x x
       have i₂ := eq11565
       grind)
    | exact superpose eq11565 eq1125
    | exact resolve eq1125 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq11774 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11336 eq11355
    | exact resolve eq11355 eq11336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336 eq11355
  have eq11799 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq11774
  have eq11837 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11799 eq220
    | exact resolve eq220 eq11799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq13468 : (M.op (σ x) (σ y)) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11635 eq11799
    | exact resolve eq11799 eq11635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11635 eq11799
  have eq13498 : (M.op (σ x) (σ y)) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13468
  have eq13552 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11565
       have i₂ := eq13498
       grind)
    | exact superpose eq13498 eq11565
    | exact resolve eq11565 eq13498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq13498
  have eq13569 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13552
  have eq13640 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13569 eq11837
    | exact resolve eq11837 eq13569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11837 eq13569
  have eq13665 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13640
  have eq13701 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13665
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13665
    | exact resolve eq13665 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13665
  have eq13702 : x = (M.op x y) := by grind
  clear eq13701
  have eq13721 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13702 eq21
    | exact resolve eq21 eq13702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq13767 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq13702 eq217
    | exact resolve eq217 eq13702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq13800 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13767
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13767
    | exact resolve eq13767 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13767
  have eq13845 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13721
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13721
    | exact resolve eq13721 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13721
  have eq13848 : x = (M.op x x) := by
    first
    | exact superpose eq13702 eq13800
    | exact resolve eq13800 eq13702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13800
  have eq13859 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13845 eq27
    | exact resolve eq27 eq13845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq14015 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7203
       have i₂ := eq13848
       grind)
    | exact superpose eq13848 eq7203
    | exact resolve eq7203 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq14033 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 x x X0 X1
       have i₂ := eq13848
       grind)
    | exact superpose eq13848 eq59
    | exact resolve eq59 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq14048 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14033 X0 X1
       have i₂ := eq13848
       grind)
    | exact superpose eq13848 eq14033
    | exact resolve eq14033 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14033
  have eq14061 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13845 eq14015
    | exact resolve eq14015 eq13845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14015
  have eq14067 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq14048 x X1
       have i₂ := eq1402 x X1
       grind)
    | (have i₁ := eq14048 x y
       have i₂ := eq1402 x X1
       grind)
    | exact superpose eq1402 eq14048
    | exact resolve eq14048 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14048
  have eq14078 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14061
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14061
    | exact resolve eq14061 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14061
  have eq14082 : ∀ X1 : G, (M.op x x) = (M.op x X1) := by
    intro X1
    first
    | exact superpose eq13702 eq14067
    | exact resolve eq14067 eq13702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14067
  have eq14091 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13845 eq14078
    | exact resolve eq14078 eq13845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13845 eq14078
  have eq14092 : ∀ X1 : G, x = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq14082 X1
       have i₂ := eq13848
       grind)
    | exact superpose eq13848 eq14082
    | exact resolve eq14082 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14082
  have eq14163 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14091 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq14091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14091
  have eq14164 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq14163
  have eq14415 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14164 eq1402
    | exact resolve eq1402 eq14164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq14419 : (σ (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq14164 eq14415
    | exact resolve eq14415 eq14164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164 eq14415
  have eq14431 : (σ (M.op x y)) = (M.op x x) := by
    first
    | exact superpose eq13702 eq14419
    | exact resolve eq14419 eq13702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13702 eq14419
  have eq14442 : x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14431
       have i₂ := eq13848
       grind)
    | exact superpose eq13848 eq14431
    | exact resolve eq14431 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13848 eq14431
  have eq14514 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq14442 eq13859
    | exact resolve eq13859 eq14442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13859
  have eq14519 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14514
       have i₂ := eq14092 sF3
       grind)
    | exact superpose eq14092 eq14514
    | exact resolve eq14514 eq14092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14092 eq14514
  have eq14775 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq14519 eq28
    | exact resolve eq28 eq14519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14519
  have eq14842 : False := by grind
  exact eq14842

/-- `Equation4646`: `(x ◇ y) ◇ x = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation4646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X1) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  clear eq36
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X3 X1)
       have i₂ := eq16 X3 X1 X0
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X2 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 x
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 X1) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op y X1)
       have i₂ := eq16 y X1 X0
       grind)
    | (have i₁ := eq174 (M.op x y)
       have i₂ := eq16 X0 y x
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op (M.op X1 y) y) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) y X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq195 X0 x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq195
    | exact resolve eq195 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq195
  have eq205 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X0 X1) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op sF3 X1)
       have i₂ := eq16 sF3 X1 x
       grind)
    | (have i₁ := eq175 (M.op x sF3)
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ x)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq175 eq214
    | exact resolve eq214 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq221 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq208 eq16
    | exact resolve eq16 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq175 eq221
    | exact resolve eq221 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq221
  have eq237 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op x y) y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) X0 X1
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X0 y)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq186 eq237
    | exact resolve eq237 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq249 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq196 eq241
    | exact resolve eq241 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq241
  have eq264 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq181 eq180
    | exact resolve eq180 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq181
  have eq270 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq208 eq266
    | exact resolve eq266 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq272 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq208 eq264
    | exact resolve eq264 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq264
  have eq280 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq215 eq270
    | exact resolve eq270 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq270
  have eq285 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq186 eq280
    | exact resolve eq280 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq280
  have eq387 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq249 X0 (M.op X0 y)
       have i₂ := eq193 X0
       grind)
    | (have i₁ := eq249 x (M.op x y)
       have i₂ := eq193 X0
       grind)
    | exact superpose eq193 eq249
    | exact resolve eq249 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq408 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq249 X1 x
       grind)
    | exact superpose eq249 eq16
    | exact resolve eq16 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq572 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq387 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) x)
       have r₂ := eq387 (M.op (M.op x y) x)
       grind)
    | exact resolve eq13 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have j0 := eq572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq610 : (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq222 eq408
    | exact resolve eq408 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq642 : (M.op (M.op x y) x) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq610
       have i₂ := eq582 (M.op sF4 sF2)
       grind)
    | exact superpose eq582 eq610
    | exact resolve eq610 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq649 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq285 eq642
    | exact resolve eq642 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq712 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq729 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq832 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq582
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq946 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1026 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq582 eq946
    | exact resolve eq946 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7361 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq712
       grind)
    | exact superpose eq712 eq39
    | exact resolve eq39 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq7362 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7361
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7361
    | exact resolve eq7361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361
  have eq7364 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq7362
    | exact resolve eq7362 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7362
  have eq21205 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq582 (M.op sF0 x)
       have i₂ := eq851 (M.op sF0 x)
       grind)
    | exact superpose eq851 eq582
    | (have j1 := eq851 X0
       grind)
    | exact resolve eq582 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq21310 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21205 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq21205 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq21205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21205
  have eq21400 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq21310 X0
       grind)
    | exact superpose eq21310 eq582
    | exact resolve eq582 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21432 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq408 X0 X0
       have i₂ := eq21310 X0
       grind)
    | exact superpose eq21310 eq408
    | exact resolve eq408 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21447 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) x))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1026 X0
       have i₂ := eq21310 (σ X0)
       grind)
    | exact superpose eq21310 eq1026
    | exact resolve eq1026 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq21468 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) x))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq21447 X0
       have i₂ := eq946 X0 (σ X0)
       grind)
    | exact superpose eq946 eq21447
    | exact resolve eq21447 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21447
  have eq21507 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq21468 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21468
    | exact resolve eq21468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21468
  have eq21579 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq21400 (σ X0)
       grind)
    | exact superpose eq21400 eq10
    | exact resolve eq10 eq21400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21400
  have eq21852 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21432 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq21432
    | exact resolve eq21432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23438 : (σ (M.op (M.op x y) x)) = (k (σ (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq649 eq21579
    | exact resolve eq21579 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21579
  have eq24110 : (M.op (M.op x y) x) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq649 eq21852
    | exact resolve eq21852 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24304 : (M.op (M.op x y) x) = (k (σ (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq24110
       have i₂ := eq582 (σ (M.op sF0 x))
       grind)
    | exact superpose eq582 eq24110
    | exact resolve eq24110 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq24110
  have eq28684 : (τ (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (τ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq24304 eq946
    | exact resolve eq946 eq24304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq28691 : (k (M.op (M.op x y) x) (M.op (M.op x y) x)) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq21507 eq28684
    | exact resolve eq28684 eq21507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21507 eq28684
  have eq28693 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq649 eq28691
    | exact resolve eq28691 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq28691
  have eq28709 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq28693 eq14
    | exact resolve eq14 eq28693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28693
  have eq37398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq7364 eq721
    | exact resolve eq721 eq7364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq7364
  have eq37405 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq37398
       have r₂ := eq27
       grind)
    | exact resolve eq37398 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37398
  have eq37411 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37405
       have i₂ := eq21310 sF3
       grind)
    | exact superpose eq21310 eq37405
    | exact resolve eq37405 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37405
  have eq37415 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37411
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq37411
    | exact resolve eq37411 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37411
  have eq37419 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37415
       have i₂ := eq21310 y
       grind)
    | exact superpose eq21310 eq37415
    | exact resolve eq37415 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37415
  have eq37421 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37419
       have i₂ := eq21310 x
       grind)
    | exact superpose eq21310 eq37419
    | exact resolve eq37419 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37419
  have eq37426 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq37421 eq115
    | exact resolve eq115 eq37421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq37421
  have eq37451 : x = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq37426
    | exact resolve eq37426 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37426
  have eq37452 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq37451
  have eq37469 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq37452 eq141
    | exact resolve eq141 eq37452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq37452
  have eq37497 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq37469
    | exact resolve eq37469 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37469
  have eq37498 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq37497
  have eq37527 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq21432 y
       have i₂ := eq37498
       grind)
    | exact superpose eq37498 eq21432
    | exact resolve eq21432 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37528 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq21852 y
       have i₂ := eq37498
       grind)
    | exact superpose eq37498 eq21852
    | exact resolve eq21852 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37498
  have eq37533 : (M.op (M.op x y) x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37528
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37528
    | exact resolve eq37528 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37528
  have eq37534 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37527
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37527
    | exact resolve eq37527 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37527
  have eq37546 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq37533
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37533
    | exact resolve eq37533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37533
  have eq37554 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq37546
    | exact resolve eq37546 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37546
  have eq37558 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37534 eq37554
    | exact resolve eq37554 eq37534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37554
  have eq37568 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq37558
       grind)
    | exact superpose eq37558 eq39
    | exact resolve eq39 eq37558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37576 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21432 x
       have i₂ := eq37558
       grind)
    | exact superpose eq37558 eq21432
    | exact resolve eq21432 eq37558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37577 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21852 x
       have i₂ := eq37558
       grind)
    | exact superpose eq37558 eq21852
    | exact resolve eq21852 eq37558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37588 : (M.op (M.op x y) x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37577
       have i₂ := eq21310 (σ x)
       grind)
    | exact superpose eq21310 eq37577
    | exact resolve eq37577 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37577
  have eq37589 : (k x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37576
       have i₂ := eq21310 x
       grind)
    | exact superpose eq21310 eq37576
    | exact resolve eq37576 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37576
  have eq37595 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37568
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37568
    | exact resolve eq37568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37568
  have eq37602 : (σ (k x x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37588
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq37588
    | exact resolve eq37588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37588
  have eq37603 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37558 eq37589
    | exact resolve eq37589 eq37558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37558 eq37589
  have eq37610 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37602
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq37602
    | exact resolve eq37602 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37602
  have eq37615 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37610
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37610
    | exact resolve eq37610 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37610
  have eq37619 : x = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37603 eq37615
    | exact resolve eq37615 eq37603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37615
  have eq37622 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq37595 eq37619
    | exact resolve eq37619 eq37595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37619
  have eq37629 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq37622 eq27
    | exact resolve eq27 eq37622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38098 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37595 eq21432
    | exact resolve eq21432 eq37595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38111 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38098
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq38098
    | exact resolve eq38098 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38098
  have eq38127 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37595 eq38111
    | exact resolve eq38111 eq37595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38111
  have eq38136 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37622 eq38127
    | exact resolve eq38127 eq37622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38127
  have eq38157 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37603 eq387
    | exact resolve eq387 eq37603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq38361 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37622 eq38157
    | exact resolve eq38157 eq37622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38157
  have eq38532 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38136 eq205
    | exact resolve eq205 eq38136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq38136
  have eq38539 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38532
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq38532
    | exact resolve eq38532 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38532
  have eq38558 : (M.op (M.op x y) x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq285 eq38539
    | exact resolve eq38539 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq38539
  have eq38575 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37595 eq38558
    | exact resolve eq38558 eq37595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37595 eq38558
  have eq38591 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq38575
    | exact resolve eq38575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq38575
  have eq38599 : x = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37603 eq38591
    | exact resolve eq38591 eq37603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37603 eq38591
  have eq38602 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37622 eq38599
    | exact resolve eq38599 eq37622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37622 eq38599
  have eq38616 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38602
  have eq39018 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq37534 eq28709
    | exact resolve eq28709 eq37534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28709 eq37534
  have eq39061 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq39018
    | exact resolve eq39018 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39018
  have eq39242 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq39061
       grind)
    | exact superpose eq39061 eq39
    | exact resolve eq39 eq39061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39250 : (M.op (M.op x y) x) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq21432 x
       have i₂ := eq39061
       grind)
    | exact superpose eq39061 eq21432
    | exact resolve eq21432 eq39061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39251 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq21852 x
       have i₂ := eq39061
       grind)
    | exact superpose eq39061 eq21852
    | exact resolve eq21852 eq39061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21852
  have eq39262 : (M.op (M.op x y) x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39251
       have i₂ := eq21310 (σ x)
       grind)
    | exact superpose eq21310 eq39251
    | exact resolve eq39251 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39251
  have eq39263 : (k x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39250
       have i₂ := eq21310 x
       grind)
    | exact superpose eq21310 eq39250
    | exact resolve eq39250 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39250
  have eq39269 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39242
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39242
    | exact resolve eq39242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39242
  have eq39276 : (σ (k x x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39262
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq39262
    | exact resolve eq39262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39262
  have eq39277 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39061 eq39263
    | exact resolve eq39263 eq39061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39061 eq39263
  have eq39284 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39276
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq39276
    | exact resolve eq39276 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq39276
  have eq39289 : (k (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq39284
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39284
    | exact resolve eq39284 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39284
  have eq39293 : x = (k (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39277 eq39289
    | exact resolve eq39289 eq39277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39277 eq39289
  have eq39296 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39269 eq39293
    | exact resolve eq39293 eq39269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39293
  have eq39299 : x = (σ x) := by
    first
    | (have r₁ := eq39296
       have r₂ := eq37629
       grind)
    | exact resolve eq39296 eq37629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37629 eq39296
  have eq39305 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq18
    | exact resolve eq18 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq39306 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq22
    | exact resolve eq22 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq39549 : (σ x) = (τ (σ x)) := by
    first
    | exact superpose eq39306 eq15
    | exact resolve eq15 eq39306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39306
  have eq39899 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39305 eq38361
    | exact resolve eq38361 eq39305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38361
  have eq39936 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq39899
       have r₂ := eq38616
       grind)
    | exact resolve eq39899 eq38616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38616 eq39899
  have eq39948 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq39936 eq27
    | exact resolve eq27 eq39936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41182 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39269 eq730
    | (have j0 := eq730 (σ x)
       grind)
    | (have r₁ := eq730 (σ x)
       have r₂ := eq39269
       grind)
    | exact resolve eq730 eq39269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq41190 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39269 eq21432
    | exact resolve eq21432 eq39269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21432 eq39269
  have eq41198 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq41182
  have eq41203 : (M.op (M.op x y) x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq41190
       have r₂ := eq39948
       grind)
    | exact resolve eq41190 eq39948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41190
  have eq41210 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq41198
       have r₂ := eq39948
       grind)
    | exact resolve eq41198 eq39948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41198
  have eq41220 : (k (σ x) (σ x)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq41203
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq41203
    | exact resolve eq41203 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41203
  have eq41226 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq41210
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq41210
    | exact resolve eq41210 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41210
  have eq41236 : (k (σ x) (σ x)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq41220
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq41220
    | exact resolve eq41220 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41220
  have eq41250 : (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq41226 eq41236
    | exact resolve eq41236 eq41226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41236
  have eq41374 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq41250 eq182
    | exact resolve eq182 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41378 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ x)) y) := by
    first
    | exact superpose eq41250 eq187
    | exact resolve eq187 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq41382 : (M.op (M.op x y) x) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq41250 eq408
    | exact resolve eq408 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41383 : (M.op (M.op x y) (σ x)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq41382
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq41382
    | exact resolve eq41382 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41382
  have eq41387 : (M.op (M.op x y) x) = (M.op (k (σ x) (σ x)) y) := by
    first
    | (have i₁ := eq41378
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq41378
    | exact resolve eq41378 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41378
  have eq41391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (σ x) (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41374 X0 X1
       have i₂ := eq21310 sF2
       grind)
    | exact superpose eq21310 eq41374
    | exact resolve eq41374 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41374
  have eq41402 : (σ x) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq41250 eq41383
    | exact resolve eq41383 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41383
  have eq41406 : (M.op (M.op x y) x) = (M.op (σ x) y) := by
    first
    | exact superpose eq41226 eq41387
    | exact resolve eq41387 eq41226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41387
  have eq41410 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq41226 eq41391
    | exact resolve eq41391 eq41226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41226 eq41391
  have eq41423 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq39305 eq41406
    | exact resolve eq41406 eq39305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39305 eq41406
  have eq41426 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq41410 x X1
       have i₂ := eq408 x X1
       grind)
    | (have i₁ := eq41410 x y
       have i₂ := eq408 x X1
       grind)
    | exact superpose eq408 eq41410
    | exact resolve eq41410 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41410
  have eq41437 : (M.op x y) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq41423
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq41423
    | exact resolve eq41423 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41423
  have eq41438 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (M.op x y) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq41426 X1
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq41426
    | exact resolve eq41426 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41426
  have eq41445 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq41250 eq41438
    | exact resolve eq41438 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41438
  have eq41457 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq41402 eq182
    | exact resolve eq182 eq41402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq41476 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq41402 eq41457
    | exact resolve eq41457 eq41402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41402 eq41457
  have eq41496 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq41445 eq41476
    | exact resolve eq41476 eq41445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41445 eq41476
  have eq41523 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq41437 eq41250
    | exact resolve eq41250 eq41437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41542 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41437 eq408
    | exact resolve eq408 eq41437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq41437
  have eq41543 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq41542
       have i₂ := eq21310 sF0
       grind)
    | exact superpose eq21310 eq41542
    | exact resolve eq41542 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41542
  have eq41559 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq41543
       have i₂ := eq39299
       grind)
    | exact superpose eq39299 eq41543
    | exact resolve eq41543 eq39299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39299 eq41543
  have eq41572 : (σ x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41250 eq41559
    | exact resolve eq41559 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41250 eq41559
  have eq41582 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41523 eq41572
    | exact resolve eq41572 eq41523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41572
  have eq41596 : x = (τ (M.op x y)) := by
    first
    | exact superpose eq41523 eq29
    | exact resolve eq29 eq41523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41634 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq41523 eq272
    | exact resolve eq272 eq41523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq41672 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq41523 eq39549
    | exact resolve eq39549 eq41523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39549
  have eq41701 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq39936 eq41634
    | exact resolve eq41634 eq39936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39936 eq41634
  have eq41739 : x = (M.op x y) := by
    first
    | exact superpose eq41672 eq41596
    | exact resolve eq41596 eq41672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41596 eq41672
  have eq41761 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41701 X0 X1
       have i₂ := eq21310 sF0
       grind)
    | exact superpose eq21310 eq41701
    | exact resolve eq41701 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310 eq41701
  have eq41814 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq41582 eq41761
    | exact resolve eq41761 eq41582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41582 eq41761
  have eq41854 : ∀ X1 : G, (σ x) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq41814 x X1
       have i₂ := eq41496 x X1
       grind)
    | exact superpose eq41496 eq41814
    | exact resolve eq41814 eq41496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41496 eq41814
  have eq41877 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq41523 eq41854
    | exact resolve eq41854 eq41523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41523 eq41854
  have eq41977 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq23438
       have i₂ := eq41739
       grind)
    | exact superpose eq41739 eq23438
    | exact resolve eq23438 eq41739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438
  have eq41981 : (M.op (M.op x y) (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq24304
       have i₂ := eq41739
       grind)
    | exact superpose eq41739 eq24304
    | exact resolve eq24304 eq41739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24304 eq41739
  have eq42040 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq41877 eq41981
    | exact resolve eq41981 eq41877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41981
  have eq42044 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq41877 eq41977
    | exact resolve eq41977 eq41877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41877 eq41977
  have eq42147 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20 eq42040
    | exact resolve eq42040 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42040
  have eq42149 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20 eq42044
    | exact resolve eq42044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42044
  have eq42209 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq42147 eq42149
    | exact resolve eq42149 eq42147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42147 eq42149
  have eq42238 : False := by grind
  exact eq42238

/-- `Equation4670`: `(x ◇ y) ◇ y = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation4670 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X3) X3) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq37
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq216 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ x) (σ y)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq47 (M.op x X1) X1
       have i₂ := eq47 x X1
       grind)
    | (have i₁ := eq47 (M.op x y) y
       have i₂ := eq47 x X1
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq831 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq841 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq837 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq837 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq837 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq837 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq6307 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq852
  have eq6421 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6422 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq6865 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6422 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6422
    | (have j0 := eq6422 y
       grind)
    | exact resolve eq6422 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6872 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (σ X0) (σ X0)
       have i₂ := eq6422 X0
       grind)
    | exact superpose eq6422 eq47
    | exact resolve eq47 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6920 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq6865
       grind)
    | exact superpose eq6865 eq16
    | exact resolve eq16 eq6865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq7941 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq217 eq6872
    | exact resolve eq6872 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8073 : (M.op (M.op x y) y) = (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq7941
       have i₂ := eq6422 (M.op sF0 y)
       grind)
    | exact superpose eq6422 eq7941
    | exact resolve eq7941 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422 eq7941
  have eq8081 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq217 eq8073
    | exact resolve eq8073 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073
  have eq8084 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq8081 eq16
    | exact resolve eq16 eq8081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq11325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11324
    | exact resolve eq11324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq11338 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11325
       have r₂ := eq28
       grind)
    | exact resolve eq11325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq11341 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11338
    | exact resolve eq11338 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11338
  have eq11343 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11341 eq6920
    | exact resolve eq6920 eq11341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920 eq11341
  have eq11355 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq11343
    | exact resolve eq11343 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11343
  have eq11356 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11355
  have eq11363 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6872 y
       have i₂ := eq11356
       grind)
    | exact superpose eq11356 eq6872
    | exact resolve eq6872 eq11356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6872
  have eq11365 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47 y y
       have i₂ := eq11356
       grind)
    | exact superpose eq11356 eq47
    | exact resolve eq47 eq11356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq11356
  have eq11371 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11365
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11365
    | exact resolve eq11365 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq11372 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11363
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11363
    | exact resolve eq11363 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11363
  have eq11376 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11372
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11372
    | exact resolve eq11372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11372
  have eq11377 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11376
    | exact resolve eq11376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376
  have eq11576 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11371 eq8081
    | exact resolve eq8081 eq11371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11585 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq11576
    | exact resolve eq11576 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11576
  have eq11587 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11585 eq216
    | exact resolve eq216 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11590 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11587
    | exact resolve eq11587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq11797 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11377 eq11371
    | exact resolve eq11371 eq11377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371 eq11377
  have eq11804 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11797
  have eq11810 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11804 eq216
    | exact resolve eq216 eq11804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq11812 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq11814 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11810
    | exact resolve eq11810 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11810
  have eq12916 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11590 eq217
    | exact resolve eq217 eq11590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12923 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11590 eq8084
    | exact resolve eq8084 eq11590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11590
  have eq13001 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11585 eq12923
    | exact resolve eq12923 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12923
  have eq13034 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq13001
  have eq13036 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq13034
    | exact resolve eq13034 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13034
  have eq13487 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11814 eq217
    | exact resolve eq217 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13494 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11814 eq8084
    | exact resolve eq8084 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq11814
  have eq13575 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11804 eq13494
    | exact resolve eq13494 eq11804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13494
  have eq13610 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq13575
  have eq13612 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13610
       have r₂ := eq11812
       grind)
    | exact resolve eq13610 eq11812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13610
  have eq13613 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq13612
    | exact resolve eq13612 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13612
  have eq13616 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq13613 eq28
    | exact resolve eq28 eq13613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13613
  have eq13636 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13616
       have r₂ := eq13036
       grind)
    | exact resolve eq13616 eq13036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13036 eq13616
  have eq14028 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11585 eq12916
    | exact resolve eq12916 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585 eq12916
  have eq14040 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14028
  have eq14083 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11804 eq13487
    | exact resolve eq13487 eq11804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11804 eq13487
  have eq14097 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14083
  have eq14103 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14097 X0
       grind)
    | (have r₁ := eq14097 X0
       have r₂ := eq11812
       grind)
    | exact resolve eq14097 eq11812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11812 eq14097
  have eq14139 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13636 eq14040
    | exact resolve eq14040 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14040
  have eq14157 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14139
  have eq14225 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13636 eq14103
    | exact resolve eq14103 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636 eq14103
  have eq14243 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14225
  have eq14848 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14157 y
       grind)
    | exact superpose eq14157 eq19
    | (have j1 := eq14157 y
       grind)
    | exact resolve eq19 eq14157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14157
  have eq14860 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq14848
  have eq15934 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14243 y
       grind)
    | exact superpose eq14243 eq19
    | (have j1 := eq14243 y
       grind)
    | exact resolve eq19 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14243
  have eq15946 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15934
  have eq15960 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15946 eq28
    | exact resolve eq28 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946
  have eq15984 : x = (M.op x y) := by
    first
    | (have r₁ := eq15960
       have r₂ := eq14860
       grind)
    | exact resolve eq15960 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860 eq15960
  have eq15985 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15984 eq21
    | exact resolve eq21 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16031 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq15984 eq217
    | exact resolve eq217 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq16046 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15984 eq8081
    | exact resolve eq8081 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8081
  have eq16050 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq16046
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16046
    | exact resolve eq16046 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16046
  have eq16065 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16031 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16031
    | (have j0 := eq16031 X0
       grind)
    | exact resolve eq16031 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16031
  have eq16110 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15985
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15985
    | exact resolve eq15985 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15985
  have eq16112 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq16050
    | exact resolve eq16050 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16050
  have eq16119 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq15984 eq16065
    | exact resolve eq16065 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16065
  have eq16120 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq15984 eq16112
    | exact resolve eq16112 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984 eq16112
  have eq16128 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16110 eq27
    | exact resolve eq27 eq16110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16110
  have eq16780 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq16120 eq16128
    | exact resolve eq16128 eq16120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16128
  have eq16781 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16780
       have i₂ := eq16119 sF3
       grind)
    | exact superpose eq16119 eq16780
    | exact resolve eq16780 eq16119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16119 eq16780
  have eq16786 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq16781 eq28
    | exact resolve eq28 eq16781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16781
  have eq16816 : False := by grind
  exact eq16816

/-- `Equation4670`: `(x ◇ y) ◇ y = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation4670 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X3) X3) := by
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
  clear eq36
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ x) (σ y)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq180 (M.op x X1) X1
       have i₂ := eq180 x X1
       grind)
    | (have i₁ := eq180 (M.op x y) y
       have i₂ := eq180 x X1
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq187 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq187 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq347 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq187 (M.op sF0 y)
       have i₂ := eq246 (M.op sF0 y)
       grind)
    | exact superpose eq246 eq187
    | exact resolve eq187 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq246
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1876 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq39
    | exact resolve eq39 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1877 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1876
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1876
    | exact resolve eq1876 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1879 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1877
    | exact resolve eq1877 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq16099 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq246 (M.op sF0 y)
       have i₂ := eq1016 (M.op sF0 y)
       grind)
    | exact superpose eq1016 eq246
    | (have j1 := eq1016 X0
       grind)
    | exact resolve eq246 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq16214 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16099 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16099 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq16099 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16099
  have eq16314 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0
       have i₂ := eq16214 X0
       grind)
    | exact superpose eq16214 eq180
    | exact resolve eq180 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16320 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq16214 X0
       grind)
    | exact superpose eq16214 eq246
    | exact resolve eq246 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16373 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16314 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16314
    | exact resolve eq16314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16448 : ∀ X0 : G, (k (σ X0) (M.op (M.op x y) y)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq16320 (σ X0)
       grind)
    | exact superpose eq16320 eq10
    | exact resolve eq10 eq16320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16320
  have eq18272 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq347 eq16373
    | exact resolve eq16373 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18439 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq18272
       have i₂ := eq246 (σ (M.op sF0 y))
       grind)
    | exact superpose eq246 eq18272
    | exact resolve eq18272 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq18272
  have eq18967 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq347 eq16448
    | exact resolve eq16448 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq16448
  have eq19239 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq18439 eq18967
    | exact resolve eq18967 eq18439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18439 eq18967
  have eq28726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1879 eq1009
    | exact resolve eq1009 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq1879
  have eq28733 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28726
       have r₂ := eq27
       grind)
    | exact resolve eq28726 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28726
  have eq28739 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28733
       have i₂ := eq16214 sF3
       grind)
    | exact superpose eq16214 eq28733
    | exact resolve eq28733 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28733
  have eq28743 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28739
       have i₂ := eq16214 sF2
       grind)
    | exact superpose eq16214 eq28739
    | exact resolve eq28739 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28739
  have eq28747 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28743
       have i₂ := eq16214 y
       grind)
    | exact superpose eq16214 eq28743
    | exact resolve eq28743 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28743
  have eq28749 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq28747
       have i₂ := eq16214 x
       grind)
    | exact superpose eq16214 eq28747
    | exact resolve eq28747 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28747
  have eq28754 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq28749 eq115
    | exact resolve eq115 eq28749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq28749
  have eq28781 : x = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq28754
    | exact resolve eq28754 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28754
  have eq28782 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq28781
  have eq28799 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq28782 eq141
    | exact resolve eq141 eq28782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq28782
  have eq28829 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq28799
    | exact resolve eq28799 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28799
  have eq28830 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq28829
  have eq28860 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16314 y
       have i₂ := eq28830
       grind)
    | exact superpose eq28830 eq16314
    | exact resolve eq16314 eq28830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28862 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16373 y
       have i₂ := eq28830
       grind)
    | exact superpose eq28830 eq16373
    | exact resolve eq16373 eq28830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28830
  have eq28867 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq28862
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28862
    | exact resolve eq28862 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28862
  have eq28868 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq28860
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28860
    | exact resolve eq28860 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28860
  have eq28880 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq28867
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28867
    | exact resolve eq28867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28867
  have eq28888 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq28880
    | exact resolve eq28880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28880
  have eq28892 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28868 eq28888
    | exact resolve eq28888 eq28868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28888
  have eq28902 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq28892
       grind)
    | exact superpose eq28892 eq39
    | exact resolve eq39 eq28892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28910 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16314 x
       have i₂ := eq28892
       grind)
    | exact superpose eq28892 eq16314
    | exact resolve eq16314 eq28892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28912 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16373 x
       have i₂ := eq28892
       grind)
    | exact superpose eq28892 eq16373
    | exact resolve eq16373 eq28892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28923 : (M.op (M.op x y) y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28912
       have i₂ := eq16214 (σ x)
       grind)
    | exact superpose eq16214 eq28912
    | exact resolve eq28912 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28912
  have eq28924 : (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28910
       have i₂ := eq16214 x
       grind)
    | exact superpose eq16214 eq28910
    | exact resolve eq28910 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28910
  have eq28931 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28902
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28902
    | exact resolve eq28902 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28902
  have eq28938 : (σ (k x x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28923
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq28923
    | exact resolve eq28923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28923
  have eq28939 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28892 eq28924
    | exact resolve eq28924 eq28892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28892 eq28924
  have eq28947 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28938
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq28938
    | exact resolve eq28938 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28938
  have eq28952 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28947
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28947
    | exact resolve eq28947 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28947
  have eq28956 : x = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28939 eq28952
    | exact resolve eq28952 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28952
  have eq28959 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq28931 eq28956
    | exact resolve eq28956 eq28931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28956
  have eq29414 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28931 eq16314
    | exact resolve eq16314 eq28931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29428 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29414
       have i₂ := eq16214 sF2
       grind)
    | exact superpose eq16214 eq29414
    | exact resolve eq29414 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29414
  have eq29445 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28931 eq29428
    | exact resolve eq29428 eq28931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28931 eq29428
  have eq29466 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28939 eq187
    | exact resolve eq187 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq29534 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28939 eq181
    | exact resolve eq181 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq28939
  have eq29537 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq186 eq29534
    | exact resolve eq29534 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29534
  have eq29600 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28959 eq29466
    | exact resolve eq29466 eq28959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28959 eq29466
  have eq29603 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29537
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29537
    | exact resolve eq29537 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29537
  have eq29836 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29600 eq26
    | (have j1 := eq29600 (σ y)
       grind)
    | exact resolve eq26 eq29600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq29600
  have eq29880 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq29836
  have eq29952 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29603 eq29445
    | exact resolve eq29445 eq29603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29445 eq29603
  have eq29959 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq29952
  have eq29965 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29959
       have r₂ := eq29880
       grind)
    | exact resolve eq29959 eq29880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29880 eq29959
  have eq30011 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq29965 eq186
    | exact resolve eq186 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq30012 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq29965 eq27
    | exact resolve eq27 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29965
  have eq30908 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op x y) (σ y)) y) := by
    intro X0 X1
    first
    | exact superpose eq30011 eq16
    | exact resolve eq16 eq30011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30909 : (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) y) := by
    first
    | exact superpose eq30011 eq180
    | exact resolve eq180 eq30011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30914 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq30909 eq30908
    | exact resolve eq30908 eq30909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30908 eq30909
  have eq32037 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq30914 X0 X0
       have i₂ := eq16214 X0
       grind)
    | exact superpose eq16214 eq30914
    | exact resolve eq30914 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30914
  have eq32352 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq28868 eq19239
    | exact resolve eq19239 eq28868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19239 eq28868
  have eq32377 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq32352
    | exact resolve eq32352 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32352
  have eq32415 : x = (k x x) := by
    first
    | (have r₁ := eq32377
       have r₂ := eq30012
       grind)
    | exact resolve eq32377 eq30012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32377
  have eq32436 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq32415
       grind)
    | exact superpose eq32415 eq39
    | exact resolve eq39 eq32415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32445 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq16314 x
       have i₂ := eq32415
       grind)
    | exact superpose eq32415 eq16314
    | exact resolve eq16314 eq32415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16314
  have eq32447 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16373 x
       have i₂ := eq32415
       grind)
    | exact superpose eq32415 eq16373
    | exact resolve eq16373 eq32415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16373
  have eq32451 : (M.op x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq32037 x
       have i₂ := eq32415
       grind)
    | exact superpose eq32415 eq32037
    | exact resolve eq32037 eq32415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32037
  have eq32459 : (k x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq32451
       have i₂ := eq16214 x
       grind)
    | exact superpose eq16214 eq32451
    | exact resolve eq32451 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32451
  have eq32463 : (M.op (M.op x y) y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32447
       have i₂ := eq16214 (σ x)
       grind)
    | exact superpose eq16214 eq32447
    | exact resolve eq32447 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32447
  have eq32464 : (k x x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32445
       have i₂ := eq16214 x
       grind)
    | exact superpose eq16214 eq32445
    | exact resolve eq32445 eq16214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16214 eq32445
  have eq32471 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32436
    | exact resolve eq32436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32436
  have eq32476 : x = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq32459
       have i₂ := eq32415
       grind)
    | exact superpose eq32415 eq32459
    | exact resolve eq32459 eq32415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32459
  have eq32480 : (σ (k x x)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32463
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq32463
    | exact resolve eq32463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32463
  have eq32481 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq32464
       have i₂ := eq32415
       grind)
    | exact superpose eq32415 eq32464
    | exact resolve eq32464 eq32415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32415 eq32464
  have eq32490 : (σ (k x x)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq30011 eq32480
    | exact resolve eq32480 eq30011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30011 eq32480
  have eq32497 : x = (σ (k x x)) := by
    first
    | exact superpose eq32476 eq32490
    | exact resolve eq32490 eq32476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32476 eq32490
  have eq32502 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32497
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq32497
    | exact resolve eq32497 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq32497
  have eq32506 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32502
    | exact resolve eq32502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32502
  have eq32509 : x = (σ x) := by
    first
    | exact superpose eq32471 eq32506
    | exact resolve eq32506 eq32471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32471 eq32506
  have eq33606 : x = (M.op x y) := by
    first
    | exact superpose eq32481 eq180
    | exact resolve eq180 eq32481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq32481
  have eq33613 : x = (M.op x y) := by
    first
    | (have i₁ := eq33606
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33606
    | exact resolve eq33606 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq33606
  have eq33739 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq33613
       grind)
    | exact superpose eq33613 eq22
    | exact resolve eq22 eq33613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33772 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq32509
       have i₂ := eq33613
       grind)
    | exact superpose eq33613 eq32509
    | exact resolve eq32509 eq33613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32509 eq33613
  have eq33794 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33772 eq33739
    | exact resolve eq33739 eq33772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33739 eq33772
  have eq37579 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33794 eq20
    | exact resolve eq20 eq33794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33794
  have eq37737 : False := by grind
  exact eq37737

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation575 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq265 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq266 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq1090 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273
    | exact resolve eq273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq273 x y
       grind)
    | exact superpose eq273 eq16
    | (have j1 := eq273 x y
       grind)
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq1123 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1090
    | (have j0 := eq1090 X0 X1
       grind)
    | exact resolve eq1090 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1090
  have eq1264 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1123 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1123
    | exact resolve eq1123 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1097
       have i₂ := eq1264 x y
       grind)
    | exact superpose eq1264 eq1097
    | (have j1 := eq1264 (σ x) (σ y)
       grind)
    | (have r₁ := eq1097
       have r₂ := eq1264 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1097
       have r₂ := eq1264 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1097 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq1264
  have eq1460 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1457
  have eq1809 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1460
       grind)
    | exact superpose eq1460 eq10
    | exact resolve eq10 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1847 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1809
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1809
    | exact resolve eq1809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1848 : x = y := by grind
  clear eq1847
  have eq1850 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1848
       grind)
    | exact superpose eq1848 eq16
    | exact resolve eq16 eq1848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1851 : False := by grind
  exact eq1851
