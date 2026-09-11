import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq67 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq404 y x
       grind)
    | exact superpose eq404 eq16
    | (have j1 := eq404 y y
       grind)
    | exact resolve eq16 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq404 X0 X0
       grind)
    | exact superpose eq404 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq404 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq404 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq404 X0 X1
       grind)
    | exact resolve eq12 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq404 X0 X0
       grind)
    | exact superpose eq404 eq67
    | (have j1 := eq404 X0 X0
       grind)
    | exact resolve eq67 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq469 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq404 X0 X1
       grind)
    | exact superpose eq404 eq9
    | (have j1 := eq404 X0 X0
       grind)
    | exact resolve eq9 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq404 X0 X1
       grind)
    | exact superpose eq404 eq9
    | (have j1 := eq404 X0 X0
       grind)
    | exact resolve eq9 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq488 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq490 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq492 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq490 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq490 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq490 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq499 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq492 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq492
    | (have j0 := eq492 (τ X0) X1
       grind)
    | exact resolve eq492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq492
  have eq501 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq499 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq499
    | (have j0 := eq499 X0 X1
       grind)
    | exact resolve eq499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq504 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq501
    | (have j0 := eq501 X0 X1
       grind)
    | exact resolve eq501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq510 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq504 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq504
    | (have j0 := eq504 (τ X0) X1
       grind)
    | exact resolve eq504 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq1357 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq488 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq488
    | exact resolve eq488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq1391 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1357 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1357
    | (have j0 := eq1357 X0
       grind)
    | exact resolve eq1357 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1357
  have eq1395 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1391 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1391
    | (have j0 := eq1391 X0
       grind)
    | exact resolve eq1391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1402 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1395 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1395
    | (have j0 := eq1395 (τ X0)
       grind)
    | exact resolve eq1395 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5211 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq461
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq461
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq461 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq5214 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq5211
  have eq5416 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq470
    | (have j0 := eq470 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq470 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq5521 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5416 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5416
    | (have j0 := eq5416 X0 X0 X2
       grind)
    | exact resolve eq5416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416
  have eq5528 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5521 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5521
    | (have j0 := eq5521 X0 X0 X2
       grind)
    | exact resolve eq5521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5521
  have eq5533 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5528 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5528
    | (have j0 := eq5528 X0 X1 X2
       grind)
    | exact resolve eq5528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq5538 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5533 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5533
    | (have j0 := eq5533 X0 X1 X2
       grind)
    | exact resolve eq5533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5533
  have eq5719 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq469
    | (have j0 := eq469 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq469 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq469
  have eq5836 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5719 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5719
    | (have j0 := eq5719 X0 X0 X2
       grind)
    | exact resolve eq5719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719
  have eq5845 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X1 X2)) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5836 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5836
    | (have j0 := eq5836 X0 X0 X2
       grind)
    | exact resolve eq5836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5836
  have eq5852 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5845 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5845
    | (have j0 := eq5845 X0 X0 X2
       grind)
    | exact resolve eq5845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5845
  have eq5859 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5852 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5852
    | (have j0 := eq5852 X0 X1 X2
       grind)
    | exact resolve eq5852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852
  have eq5864 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5859 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5859
    | (have j0 := eq5859 X0 X1 X2
       grind)
    | exact resolve eq5859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5859
  have eq11516 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (k X1 X0)
       have i₂ := eq5538 X1 X0 X0
       grind)
    | exact superpose eq5538 eq73
    | (have j1 := eq5538 X1 X1 x
       grind)
    | exact resolve eq73 eq5538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq12044 : ∀ X0 X1 : G, (k X0 X1) = (M.op (M.op (k X0 X1) X0) (k X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83 (k X0 X1) X1 X0
       have i₂ := eq5864 X0 X1 (k X0 X1)
       grind)
    | exact superpose eq5864 eq83
    | (have j1 := eq5864 X0 X0 x
       grind)
    | exact resolve eq83 eq5864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq5864
  have eq17929 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5214
       grind)
    | exact superpose eq5214 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5214
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5214
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq5214
       grind)
    | exact resolve eq12 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq18045 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq17929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17929
  have eq26825 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12044 X0 X0
       have i₂ := eq1395 X0
       grind)
    | exact superpose eq1395 eq12044
    | (have j0 := eq12044 X0 X0
       have j1 := eq1395 X0
       grind)
    | exact resolve eq12044 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395 eq12044
  have eq26953 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26825 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26825
  have eq26956 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26953 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26953
    | (have j0 := eq26953 (σ X0)
       grind)
    | exact resolve eq26953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26953
  have eq42081 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq18045 X1
       grind)
    | exact superpose eq18045 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq18045 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq18045 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq18045 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq18045 X0
       grind)
    | exact resolve eq12 eq18045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18045
  have eq42250 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq42081 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42081
  have eq42355 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1402 (σ y)
       have i₂ := eq42250 X0 (σ y)
       grind)
    | exact superpose eq42250 eq1402
    | (have j0 := eq1402 (σ y)
       have j1 := eq42250 X0 x
       grind)
    | exact resolve eq1402 eq42250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42250
  have eq42469 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq42355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42355
  have eq42529 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42469 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq42469
    | (have j0 := eq42469 X0
       grind)
    | exact resolve eq42469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42469
  have eq42530 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq42529 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42529
  have eq42587 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq510 (σ x) X0
       have i₂ := eq42530 (σ x)
       grind)
    | exact superpose eq42530 eq510
    | (have j0 := eq510 (σ x) X0
       grind)
    | exact resolve eq510 eq42530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq42597 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1402 (σ x)
       have i₂ := eq42530 (σ x)
       grind)
    | exact superpose eq42530 eq1402
    | (have j0 := eq1402 (σ x)
       grind)
    | exact resolve eq1402 eq42530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq42530
  have eq42711 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq42597
  have eq42721 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq42587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42587
  have eq42771 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq42711
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42711
    | exact resolve eq42711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42711
  have eq42772 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq42771
  have eq42778 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42721 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42721
    | exact resolve eq42721 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42721
  have eq42799 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq42778 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq42778 X0
       have r₂ := eq12 X0 y
       grind)
    | (have r₁ := eq42778 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42778 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42778
  have eq42807 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq42772
       grind)
    | exact superpose eq42772 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq42772
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq42772
       grind)
    | exact resolve eq12 eq42772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42812 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq42772
       grind)
    | exact superpose eq42772 eq73
    | exact resolve eq73 eq42772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42895 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq384 y y x
       have i₂ := eq42772
       grind)
    | exact superpose eq42772 eq384
    | exact resolve eq384 eq42772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42772
  have eq42976 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq42807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42807
  have eq43006 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42895 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq42895
    | exact resolve eq42895 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42895
  have eq43047 : ∀ X0 X1 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq42799 X1
       grind)
    | exact superpose eq42799 eq12
    | (have j0 := eq12 X0 y
       have j1 := eq42799 X1
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq42799 X0
       grind)
    | exact resolve eq12 eq42799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42799
  have eq43216 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43047 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43047
  have eq43292 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq42976 X1
       grind)
    | exact superpose eq42976 eq73
    | (have j1 := eq42976 X1
       grind)
    | exact resolve eq73 eq42976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43375 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384 x x x
       have i₂ := eq42976 X0
       grind)
    | exact superpose eq42976 eq384
    | (have j1 := eq42976 X1
       grind)
    | exact resolve eq384 eq42976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42976
  have eq43486 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43375 X0 X1
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq43375
    | (have j0 := eq43375 X0 X1
       grind)
    | exact resolve eq43375 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43375
  have eq43569 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26956 x
       have i₂ := eq43216 X0 x
       grind)
    | exact superpose eq43216 eq26956
    | (have j0 := eq26956 x
       have j1 := eq43216 X0 x
       grind)
    | exact resolve eq26956 eq43216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43216
  have eq43653 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq43569 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43569
  have eq46068 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ x) X0
       have i₂ := eq43653 X1
       grind)
    | exact superpose eq43653 eq73
    | (have j1 := eq43653 X1
       grind)
    | exact resolve eq73 eq43653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46151 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384 (σ x) (σ x) x
       have i₂ := eq43653 X0
       grind)
    | exact superpose eq43653 eq384
    | (have j1 := eq43653 X1
       grind)
    | exact resolve eq384 eq43653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43653
  have eq46263 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46151 X0 X1
       have i₂ := eq86 (σ x) X0
       grind)
    | exact superpose eq86 eq46151
    | (have j0 := eq46151 X0 X1
       grind)
    | exact resolve eq46151 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46151
  have eq47052 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42812 X0
       have i₂ := eq43006 X0
       grind)
    | exact superpose eq43006 eq42812
    | exact resolve eq42812 eq43006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42812 eq43006
  have eq47287 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47052
  have eq47318 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq47287 X1
       grind)
    | exact superpose eq47287 eq73
    | (have j1 := eq47287 X1
       grind)
    | exact resolve eq73 eq47287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47401 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384 x x x
       have i₂ := eq47287 X0
       grind)
    | exact superpose eq47287 eq384
    | (have j1 := eq47287 X1
       grind)
    | exact resolve eq384 eq47287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47287
  have eq47512 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47401 X0 X1
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq47401
    | (have j0 := eq47401 X0 X1
       grind)
    | exact resolve eq47401 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47401
  have eq52329 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (k X1 y) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43292 X0 X1
       have i₂ := eq43486 X0 X2
       grind)
    | exact superpose eq43486 eq43292
    | (have j0 := eq43292 X0 X1
       have j1 := eq43486 X0 X1
       grind)
    | exact resolve eq43292 eq43486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43292 eq43486
  have eq52566 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52329 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52329
  have eq52677 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op y y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11516 y X0
       have i₂ := eq52566 X0 X1
       grind)
    | exact superpose eq52566 eq11516
    | (have j0 := eq11516 X0 X0
       have j1 := eq52566 X0 X1
       grind)
    | exact resolve eq11516 eq52566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52566
  have eq52712 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52677 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52677
  have eq52713 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52712
  have eq52876 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384 y y x
       have i₂ := eq52713 X0
       grind)
    | exact superpose eq52713 eq384
    | (have j1 := eq52713 X1
       grind)
    | exact resolve eq384 eq52713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52713
  have eq52989 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52876 X0 X1
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq52876
    | (have j0 := eq52876 X0 X1
       grind)
    | exact resolve eq52876 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52876
  have eq59443 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47318 X0 X1
       have i₂ := eq47512 X0 X2
       grind)
    | exact superpose eq47512 eq47318
    | (have j0 := eq47318 X0 X1
       have j1 := eq47512 X0 X1
       grind)
    | exact resolve eq47318 eq47512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47318 eq47512
  have eq59687 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59443 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59443
  have eq59715 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52989 X0 X1
       have i₂ := eq59687 X0 X2
       grind)
    | exact superpose eq59687 eq52989
    | (have j0 := eq52989 X0 X1
       have j1 := eq59687 X0 X1
       grind)
    | exact resolve eq52989 eq59687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52989 eq59687
  have eq60082 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq59715 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59715
  have eq62051 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq60082 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60082
  have eq62052 : y = (M.op x y) := by grind
  clear eq62051
  have eq129529 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = X0 ∨ (k X1 y) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46068 X0 X1
       have i₂ := eq46263 X0 X2
       grind)
    | exact superpose eq46263 eq46068
    | (have j0 := eq46068 X0 X1
       have j1 := eq46263 X0 X1
       grind)
    | exact resolve eq46068 eq46263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46068 eq46263
  have eq129898 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq129529 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129529
  have eq129941 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq129898 X0 (σ y)
       grind)
    | exact superpose eq129898 eq16
    | (have j1 := eq129898 X0 x
       grind)
    | exact resolve eq16 eq129898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129898
  have eq130484 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq129941 X0
       have i₂ := eq62052
       grind)
    | exact superpose eq62052 eq129941
    | (have j0 := eq129941 X0
       grind)
    | exact resolve eq129941 eq62052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62052 eq129941
  have eq130485 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq130484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130484
  have eq130531 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26956 y
       have i₂ := eq130485 y
       grind)
    | exact superpose eq130485 eq26956
    | (have j0 := eq26956 y
       grind)
    | exact resolve eq26956 eq130485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26956
  have eq130574 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq11516 y X0
       have i₂ := eq130485 X0
       grind)
    | exact superpose eq130485 eq11516
    | (have j0 := eq11516 X0 X0
       grind)
    | exact resolve eq11516 eq130485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11516 eq130485
  have eq130619 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq130574 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130574
  have eq130620 : y = (M.op y y) := by grind
  clear eq130619
  have eq130624 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq130531
  have eq131192 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq130620
       grind)
    | exact superpose eq130620 eq73
    | exact resolve eq73 eq130620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131275 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq384 y y x
       have i₂ := eq130620
       grind)
    | exact superpose eq130620 eq384
    | exact resolve eq384 eq130620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130620
  have eq131487 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq131275 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq131275
    | exact resolve eq131275 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq131275
  have eq133566 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) X0
       have i₂ := eq130624
       grind)
    | exact superpose eq130624 eq73
    | exact resolve eq73 eq130624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq130624
  have eq136778 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq131192 X0
       have i₂ := eq131487 X0
       grind)
    | exact superpose eq131487 eq131192
    | exact resolve eq131192 eq131487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131192
  have eq136798 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq131487 X0
       have i₂ := eq136778 X0
       grind)
    | exact superpose eq136778 eq131487
    | exact resolve eq131487 eq136778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131487
  have eq136897 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq384 y X1 X0
       have i₂ := eq136778 X0
       grind)
    | exact superpose eq136778 eq384
    | exact resolve eq384 eq136778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq137554 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136897 X0 X0
       have i₂ := eq136778 X0
       grind)
    | exact superpose eq136778 eq136897
    | exact resolve eq136897 eq136778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136778 eq136897
  have eq165833 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq133566 X0
       have i₂ := eq137554 X0 (σ y)
       grind)
    | exact superpose eq137554 eq133566
    | exact resolve eq133566 eq137554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133566
  have eq166116 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq137554 X0 (σ y)
       have i₂ := eq165833 X0
       grind)
    | exact superpose eq165833 eq137554
    | exact resolve eq137554 eq165833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137554 eq165833
  have eq167775 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166116 (σ x)
       grind)
    | exact superpose eq166116 eq16
    | exact resolve eq16 eq166116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166116
  have eq167913 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq167775
       have i₂ := eq136798 x
       grind)
    | exact superpose eq136798 eq167775
    | exact resolve eq167775 eq136798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136798 eq167775
  have eq167914 : False := by grind
  exact eq167914

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
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
  clear eq56 eq58
  have eq82 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq88
  have eq253 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 X0 (σ X1)
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
  have eq262 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq266 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq262 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq262 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq262 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq277 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       have j1 := eq82 X1 (σ X0)
       grind)
    | (have r₁ := eq266 X0 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq266 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq266
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq277
    | (have j0 := eq277 X0 X1
       grind)
    | exact resolve eq277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq291 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq285 x y
       grind)
    | exact superpose eq285 eq16
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq449 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq291 X0 (τ X1)
       grind)
    | exact superpose eq291 eq18
    | exact resolve eq18 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq291
  have eq464 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq449
    | exact resolve eq449 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq471 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq464
    | exact resolve eq464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq486 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq303
       have i₂ := eq471 x y
       grind)
    | exact superpose eq471 eq303
    | exact resolve eq303 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq471
  have eq487 : False := by grind
  exact eq487

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq27 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq59 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq53 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq65 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq95 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 X0
       have i₂ := eq78 X2 X1
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq108
    | (have j0 := eq108 (σ X0)
       grind)
    | exact resolve eq108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq398 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq943 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq59
    | (have j1 := eq131 X0
       grind)
    | exact resolve eq59 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq950 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1173 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X0))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq943 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq943
    | (have j0 := eq943 (τ X0)
       grind)
    | exact resolve eq943 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq943
  have eq1209 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1173 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1173
    | (have j0 := eq1173 X0
       grind)
    | exact resolve eq1173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1210 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1209 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1209
    | (have j0 := eq1209 X0
       grind)
    | exact resolve eq1209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1211 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1210 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1210
    | (have j0 := eq1210 X0
       grind)
    | exact resolve eq1210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1580 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq398 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq398 X0 X1
       grind)
    | exact superpose eq398 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq398 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq398 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq398 X0 X1
       grind)
    | exact resolve eq13 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq1625 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1626 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq1649 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1626 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1626
    | (have j0 := eq1626 X0 X1
       grind)
    | exact resolve eq1626 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1650 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1668 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1650 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1650
    | exact resolve eq1650 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1759 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1668 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1668
    | (have j0 := eq1668 X0 X1
       grind)
    | exact resolve eq1668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1668
  have eq1761 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1759 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1759
    | (have j0 := eq1759 X1 X1
       grind)
    | exact resolve eq1759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1891 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1761 (τ X0) X1
       grind)
    | exact superpose eq1761 eq17
    | (have j1 := eq1761 X0 X1
       grind)
    | exact resolve eq17 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1907 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq1761 X0 X1
       grind)
    | exact superpose eq1761 eq12
    | (have j1 := eq1761 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1761 X0 X1
       grind)
    | exact resolve eq12 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761
  have eq1943 : ∀ X0 X1 X2 : G, (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1907 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq2024 : ∀ X0 X1 X2 : G, (τ X2) = (k X0 (τ X2)) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 X0
       have i₂ := eq1943 X1 X2 (σ X0)
       grind)
    | exact superpose eq1943 eq27
    | (have j1 := eq1943 X0 (τ X2) X0
       grind)
    | exact resolve eq27 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2059 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1943 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq2075 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2059 X0 (M.op X0 X1)
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq2059
    | (have j0 := eq2059 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq2059 X1 (M.op X1 X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq2059 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2141 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq3853 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2024 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2024
    | (have j0 := eq2024 X0 X2 (σ X0)
       grind)
    | exact resolve eq2024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq4050 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3853 X1 X2 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3853
    | (have j0 := eq3853 X1 X2 X2
       grind)
    | exact resolve eq3853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq5514 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1891 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1891
    | (have j0 := eq1891 X0 X1
       grind)
    | exact resolve eq1891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq5675 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5514 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5514
    | (have j0 := eq5514 X0 X1
       grind)
    | exact resolve eq5514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5514
  have eq10502 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq4050 x y X0
       grind)
    | exact superpose eq4050 eq16
    | (have j1 := eq4050 X0 y X0
       grind)
    | exact resolve eq16 eq4050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050
  have eq10680 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10502 X0
       have i₂ := eq5675 x y
       grind)
    | exact superpose eq5675 eq10502
    | (have j0 := eq10502 X0
       have j1 := eq5675 X0 y
       grind)
    | (have r₁ := eq10502 X0
       have r₂ := eq5675 x y
       grind)
    | exact resolve eq10502 eq5675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5675 eq10502
  have eq10682 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq10680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10680
  have eq10708 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1211 y
       have i₂ := eq10682 y
       grind)
    | exact superpose eq10682 eq1211
    | (have j0 := eq1211 y
       grind)
    | exact resolve eq1211 eq10682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq10682
  have eq10765 : y = (M.op y y) := by grind
  clear eq10708
  have eq10794 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq10765
       grind)
    | exact superpose eq10765 eq9
    | exact resolve eq9 eq10765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10805 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq95 X0 y y
       have i₂ := eq10765
       grind)
    | exact superpose eq10765 eq95
    | exact resolve eq95 eq10765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10820 : y = (k y y) := by
    first
    | (have i₁ := eq2141 y y
       have i₂ := eq10765
       grind)
    | exact superpose eq10765 eq2141
    | exact resolve eq2141 eq10765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141 eq10765
  have eq10832 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq10805 X0
       have i₂ := eq78 X0 y
       grind)
    | exact superpose eq78 eq10805
    | exact resolve eq10805 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq10805
  have eq10852 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq950 y
       have i₂ := eq10820
       grind)
    | exact superpose eq10820 eq950
    | (have j0 := eq950 y
       grind)
    | exact resolve eq950 eq10820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq10820
  have eq10875 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq10852
  have eq11370 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq10875
       grind)
    | exact superpose eq10875 eq9
    | exact resolve eq9 eq10875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq11425 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10794 X0
       have i₂ := eq10832 X0
       grind)
    | exact superpose eq10832 eq10794
    | exact resolve eq10794 eq10832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10794
  have eq11426 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10832 X0
       have i₂ := eq11425 X0
       grind)
    | exact superpose eq11425 eq10832
    | exact resolve eq10832 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10832
  have eq11441 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op y X0) X1) (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X1 y X0
       have i₂ := eq11425 X1
       grind)
    | exact superpose eq11425 eq95
    | exact resolve eq95 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq11501 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11441 X0 X1
       have i₂ := eq11425 X0
       grind)
    | exact superpose eq11425 eq11441
    | exact resolve eq11441 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11425 eq11441
  have eq13553 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11370 X0
       have i₂ := eq11501 (σ y) X0
       grind)
    | exact superpose eq11501 eq11370
    | exact resolve eq11370 eq11501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11370
  have eq13594 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11501 (σ y) X0
       have i₂ := eq13553 X0
       grind)
    | exact superpose eq13553 eq11501
    | exact resolve eq11501 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11501 eq13553
  have eq13680 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13594 (σ x)
       grind)
    | exact superpose eq13594 eq16
    | exact resolve eq16 eq13594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13594
  have eq13689 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13680
       have i₂ := eq11426 x
       grind)
    | exact superpose eq11426 eq13680
    | exact resolve eq13680 eq11426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11426 eq13680
  have eq13690 : False := by grind
  exact eq13690

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
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
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq51 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq51
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq109 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq105 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq105 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq105 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq105
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq109 (σ X0) (σ X1)
       grind)
    | exact superpose eq109 eq15
    | exact resolve eq15 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq284
    | exact resolve eq284 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq284
  have eq294 : False := by grind
  exact eq294

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq17
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X5) X4) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0 X5
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq124 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq135 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq133 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq133 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq332 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq124
    | (have j1 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq124 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq335 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq332
  have eq336 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq335
       grind)
    | exact superpose eq335 eq9
    | exact resolve eq9 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq135
    | (have j0 := eq135 (τ X0) X1
       grind)
    | exact resolve eq135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq135
  have eq548 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq551 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq597 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 (τ X0) X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq551
    | (have j0 := eq551 (τ X0) X1
       grind)
    | exact resolve eq551 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq551
  have eq755 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq773 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq755 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq755
    | exact resolve eq755 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq2015 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq97 x X0 y
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq97
    | exact resolve eq97 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq336
  have eq2104 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2015 y
       have i₂ := eq335
       grind)
    | exact superpose eq335 eq2015
    | exact resolve eq2015 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq2150 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2104
  have eq2223 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2015 y
       have i₂ := eq2150
       grind)
    | exact superpose eq2150 eq2015
    | exact resolve eq2015 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015 eq2150
  have eq2262 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2223
  have eq2343 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2262
       grind)
    | exact resolve eq12 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2379 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq4043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq2379 x
       grind)
    | exact superpose eq2379 eq124
    | exact resolve eq124 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2379
  have eq4044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4043
  have eq4045 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4044
  have eq4048 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4045
       grind)
    | exact superpose eq4045 eq16
    | exact resolve eq16 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4051 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq4045
       grind)
    | exact superpose eq4045 eq9
    | exact resolve eq9 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4098 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq773 (σ x) (σ y)
       have i₂ := eq4045
       grind)
    | exact superpose eq4045 eq773
    | exact resolve eq773 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4124 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4051 X0
       have i₂ := eq773 (σ x) X0
       grind)
    | (have i₁ := eq4051 X0
       have i₂ := eq773 (σ x) (M.op (σ x) X0)
       grind)
    | exact superpose eq773 eq4051
    | exact resolve eq4051 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4051
  have eq4196 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq4098
       grind)
    | exact superpose eq4098 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq4098
       grind)
    | exact resolve eq12 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4197 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ x) X0
       have i₂ := eq4098
       grind)
    | exact superpose eq4098 eq9
    | exact resolve eq9 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4242 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4263 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4197 X0
       have i₂ := eq773 (σ x) X0
       grind)
    | (have i₁ := eq4197 X0
       have i₂ := eq773 (σ x) (M.op (σ x) X0)
       grind)
    | exact superpose eq773 eq4197
    | exact resolve eq4197 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq4197
  have eq4386 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4242 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq4242
    | exact resolve eq4242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4401 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq597 (σ x) X0
       have i₂ := eq4242 (σ x)
       grind)
    | exact superpose eq4242 eq597
    | (have j0 := eq597 (σ x) X0
       grind)
    | exact resolve eq597 eq4242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq4242
  have eq4447 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq4401 X0
       have i₂ := eq4098
       grind)
    | exact superpose eq4098 eq4401
    | (have j0 := eq4401 X0
       grind)
    | exact resolve eq4401 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4401
  have eq4448 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq4447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447
  have eq4456 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4448 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4448
    | exact resolve eq4448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4448
  have eq4661 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4124 (σ x)
       have i₂ := eq4098
       grind)
    | exact superpose eq4098 eq4124
    | exact resolve eq4124 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4751 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4661
       have i₂ := eq4045
       grind)
    | exact superpose eq4045 eq4661
    | exact resolve eq4661 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4045 eq4661
  have eq4758 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4751
       grind)
    | exact superpose eq4751 eq10
    | exact resolve eq10 eq4751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4751
  have eq4812 : x = y := by
    first
    | (have i₁ := eq4758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4758
    | exact resolve eq4758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758
  have eq4835 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4048
       have i₂ := eq4812
       grind)
    | exact superpose eq4812 eq4048
    | exact resolve eq4048 eq4812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4048 eq4812
  have eq5196 : ∀ X3 : G, (M.op (M.op (M.op (M.op (σ x) (σ x)) X3) (σ x)) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq92 (σ x) x x x (σ x) X3
       have i₂ := eq4263 (M.op (M.op (M.op x (σ x)) (M.op x x)) x)
       grind)
    | exact superpose eq4263 eq92
    | exact resolve eq92 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5255 : ∀ X3 : G, (M.op (M.op (M.op (σ x) X3) (σ x)) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq5196 X3
       have i₂ := eq4098
       grind)
    | exact superpose eq4098 eq5196
    | exact resolve eq5196 eq4098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4098 eq5196
  have eq5258 : ∀ X3 : G, (M.op (σ x) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq5255 X3
       have i₂ := eq4263 X3
       grind)
    | exact superpose eq4263 eq5255
    | exact resolve eq5255 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5255
  have eq5271 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4263 X0
       have i₂ := eq5258 X0
       grind)
    | exact superpose eq5258 eq4263
    | exact resolve eq4263 eq5258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263 eq5258
  have eq7858 : ∀ X0 : G, (σ x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq4386 X0
       have i₂ := eq5271 (σ X0)
       grind)
    | exact superpose eq5271 eq4386
    | exact resolve eq4386 eq5271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386 eq5271
  have eq7859 : ∀ X0 : G, (σ x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq7858 X0
       have i₂ := eq4456 X0
       grind)
    | exact superpose eq4456 eq7858
    | exact resolve eq7858 eq4456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456 eq7858
  have eq7863 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4835
       have i₂ := eq7859 x
       grind)
    | exact superpose eq7859 eq4835
    | (have r₁ := eq4835
       have r₂ := eq7859 x
       grind)
    | exact resolve eq4835 eq7859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835 eq7859
  have eq7918 : False := by grind
  exact eq7918

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq40 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq45 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq45
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50
  have eq99 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq103 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq99 X1 X1
       have r₂ := eq52 X1 X1
       grind)
    | (have r₁ := eq99 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq99 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq99
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq103 (σ X1) (σ X0)
       grind)
    | exact superpose eq103 eq15
    | exact resolve eq15 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq103 X1 X0
       grind)
    | exact superpose eq103 eq261
    | exact resolve eq261 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq261
  have eq271 : False := by grind
  exact eq271

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq207 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq218 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq528 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq519 X0
       grind)
    | exact superpose eq519 eq14
    | exact resolve eq14 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq717 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq718 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq911 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq528
    | exact resolve eq528 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq528
    | exact resolve eq528 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq945 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq911 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq911
       grind)
    | exact resolve eq12 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by grind
  clear eq945
  have eq958 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq913 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq913
       grind)
    | exact resolve eq12 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq958
  have eq1073 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq955 eq130
    | exact resolve eq130 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1073
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1073
    | exact resolve eq1073 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq3561 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq718 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq718
    | (have j0 := eq718 (τ X0)
       grind)
    | exact resolve eq718 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq718
  have eq3569 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3561
    | (have j0 := eq3561 X0
       grind)
    | exact resolve eq3561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq3575 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3569 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3569
    | (have j0 := eq3569 X0
       grind)
    | exact resolve eq3569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq6239 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq6278 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6239
  have eq6282 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6278
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6278
    | exact resolve eq6278 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6278
  have eq6299 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6282
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq6282 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282
  have eq6304 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6299 eq49
    | exact resolve eq49 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6299
  have eq6429 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq6452 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6429
  have eq6455 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6452
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq6452
    | exact resolve eq6452 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq6452
  have eq6479 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6455
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq6455 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6455
  have eq6619 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq207
    | (have j0 := eq207 (M.op x y)
       grind)
    | exact resolve eq207 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq6641 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6619
  have eq6643 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq132 eq6641
    | exact resolve eq6641 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq6641
  have eq6674 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6643
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq6643 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643
  have eq6697 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6674 eq155
    | exact resolve eq155 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq12795 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6479 eq109
    | exact resolve eq109 eq6479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq6479
  have eq12810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq12810
    | exact resolve eq12810 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12810
  have eq12822 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq12811
       have r₂ := eq27
       grind)
    | exact resolve eq12811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12811
  have eq12824 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq12822
    | exact resolve eq12822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12822
  have eq12912 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12824 eq6304
    | exact resolve eq6304 eq12824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12824
  have eq13006 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq12912
    | exact resolve eq12912 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12912
  have eq13009 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3575 x
       grind)
    | (have r₁ := eq13006
       have r₂ := eq3575 x
       grind)
    | exact resolve eq13006 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13006
  have eq13010 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq13009
       grind)
    | exact superpose eq13009 eq50
    | exact resolve eq50 eq13009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13011 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq13009
       grind)
    | exact superpose eq13009 eq53
    | exact resolve eq53 eq13009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13009
  have eq13090 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq911 eq13011
    | exact resolve eq13011 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13011
  have eq13130 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13090 eq13010
    | exact resolve eq13010 eq13090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13010 eq13090
  have eq13168 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13130
  have eq13169 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13168
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13168
    | exact resolve eq13168 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13168
  have eq13170 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13169
  have eq13200 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13170 eq968
    | exact resolve eq968 eq13170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq13170
  have eq13336 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13200 eq82
    | exact resolve eq82 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq13200
  have eq13358 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq13336
    | exact resolve eq13336 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13336
  have eq13656 : (τ (σ x)) = (k x x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13358 eq6304
    | exact resolve eq6304 eq13358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13358
  have eq13758 : x = (k y x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq13656
    | exact resolve eq13656 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13656
  have eq14769 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq13758
       grind)
    | exact superpose eq13758 eq71
    | exact resolve eq71 eq13758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14779 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13758
       grind)
    | exact superpose eq13758 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq13758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13758
  have eq14780 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq3575 x
       grind)
    | (have r₁ := eq14779
       have r₂ := eq3575 x
       grind)
    | exact resolve eq14779 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14779
  have eq14790 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14769
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14769
    | exact resolve eq14769 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14769
  have eq14792 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14780
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14780
    | exact resolve eq14780 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14780
  have eq14799 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14792
    | exact resolve eq14792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq14800 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14799
  have eq14812 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq14800
       grind)
    | exact superpose eq14800 eq50
    | exact resolve eq50 eq14800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14813 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq14800
       grind)
    | exact superpose eq14800 eq53
    | exact resolve eq53 eq14800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14800
  have eq14895 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq911 eq14813
    | exact resolve eq14813 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14813
  have eq15967 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14790 eq113
    | exact resolve eq113 eq14790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq14790
  have eq15979 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq15967
  have eq15989 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq3575 x
       grind)
    | (have r₁ := eq15979
       have r₂ := eq3575 x
       grind)
    | exact resolve eq15979 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15979
  have eq15997 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq15989
       grind)
    | exact superpose eq15989 eq50
    | exact resolve eq50 eq15989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15998 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq15989
       grind)
    | exact superpose eq15989 eq53
    | exact resolve eq53 eq15989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15989
  have eq16083 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq911 eq15998
    | exact resolve eq15998 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15998
  have eq16886 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14895 eq14812
    | exact resolve eq14812 eq14895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14812 eq14895
  have eq16930 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16886
  have eq16933 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16930
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16930
    | exact resolve eq16930 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16930
  have eq16934 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16933
  have eq16954 : (σ (k y x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16934 eq130
    | exact resolve eq130 eq16934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16934
  have eq17057 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16954
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16954
    | exact resolve eq16954 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq16954
  have eq18635 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17057 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq17057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17057
  have eq18643 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18635
    | exact resolve eq18635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq18652 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18643
    | exact resolve eq18643 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18643
  have eq39164 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16083 eq15997
    | exact resolve eq15997 eq16083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15997 eq16083
  have eq39244 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq39164
  have eq39246 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39244
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39244
    | exact resolve eq39244 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39244
  have eq39247 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq39246
  have eq39268 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39247 eq141
    | exact resolve eq141 eq39247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq39333 : (k x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39247 eq6304
    | exact resolve eq6304 eq39247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39247
  have eq39376 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6697 eq39333
    | exact resolve eq39333 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39333
  have eq39416 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq155 eq39268
    | exact resolve eq39268 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq39268
  have eq39810 : (k x x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39416 eq39376
    | exact resolve eq39376 eq39416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39376 eq39416
  have eq39842 : (k x x) = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq39810
  have eq40781 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39842 eq955
    | exact resolve eq955 eq39842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39842
  have eq40807 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq3575 x
       grind)
    | (have r₁ := eq40781
       have r₂ := eq3575 x
       grind)
    | exact resolve eq40781 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40781
  have eq41105 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq40807
       grind)
    | exact superpose eq40807 eq50
    | exact resolve eq50 eq40807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq41106 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq40807
       grind)
    | exact superpose eq40807 eq53
    | exact resolve eq53 eq40807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40807
  have eq41249 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq911 eq41106
    | exact resolve eq41106 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41106
  have eq43051 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41249 eq41105
    | exact resolve eq41105 eq41249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41105 eq41249
  have eq43134 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq43051
  have eq43136 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43134
    | exact resolve eq43134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq43134
  have eq43137 : y = (M.op x y) := by grind
  clear eq43136
  have eq43138 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq43137 eq20
    | exact resolve eq20 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq43225 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq43137 eq955
    | exact resolve eq955 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq43295 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq43138
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43138
    | exact resolve eq43138 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43138
  have eq43332 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq43295 eq26
    | exact resolve eq26 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq43336 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq43295 eq51
    | exact resolve eq51 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq43353 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq43295 eq218
    | exact resolve eq218 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq47425 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq43295 eq12795
    | exact resolve eq12795 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12795
  have eq47428 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq47425
       grind)
    | exact superpose eq47425 eq16
    | exact resolve eq16 eq47425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47425
  have eq47506 : (M.op y y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6697 eq47428
    | exact resolve eq47428 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47428
  have eq47515 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq43137 eq47506
    | exact resolve eq47506 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47506
  have eq47522 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq47515
       have r₂ := eq13 x y
       grind)
    | exact resolve eq47515 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47515
  have eq141529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43295 eq18652
    | exact resolve eq18652 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18652
  have eq141530 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq141529
       have r₂ := eq27
       grind)
    | exact resolve eq141529 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141529
  have eq141531 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43137 eq141530
    | exact resolve eq141530 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141530
  have eq141535 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1077 eq141531
    | exact resolve eq141531 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq149944 : (τ (σ x)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq141535 eq6304
    | exact resolve eq6304 eq141535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6304 eq141535
  have eq150176 : x = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq149944
    | exact resolve eq149944 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq149944
  have eq150210 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have j1 := eq3575 x
       grind)
    | (have r₁ := eq150176
       have r₂ := eq3575 x
       grind)
    | exact resolve eq150176 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150176
  have eq150219 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq150210
       grind)
    | exact superpose eq150210 eq53
    | exact resolve eq53 eq150210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq150252 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq150210
       grind)
    | exact superpose eq150210 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq150210
       grind)
    | exact resolve eq13 eq150210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150210
  have eq150353 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq150252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150252
  have eq150425 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq911 eq150219
    | exact resolve eq150219 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq150219
  have eq150467 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq43137 eq150425
    | exact resolve eq150425 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150425
  have eq151075 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq150353 sF0
       grind)
    | exact superpose eq150353 eq130
    | exact resolve eq130 eq150353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq150353
  have eq151250 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq43137 eq151075
    | exact resolve eq151075 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151075
  have eq151802 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq151250
       have i₂ := eq150467
       grind)
    | exact superpose eq150467 eq151250
    | exact resolve eq151250 eq150467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150467 eq151250
  have eq151909 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq151802
  have eq151935 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq151909
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq151909
    | exact resolve eq151909 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151909
  have eq152198 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq151935 eq141531
    | exact resolve eq141531 eq151935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141531 eq151935
  have eq152210 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq152198
  have eq152278 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152210 eq54
    | exact resolve eq54 eq152210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq152301 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152210 eq43336
    | exact resolve eq43336 eq152210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43336 eq152210
  have eq152477 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq913 eq152278
    | exact resolve eq152278 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152278
  have eq154060 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152477 eq152301
    | exact resolve eq152301 eq152477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152301 eq152477
  have eq154150 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq154060
  have eq154152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43332 eq154150
    | exact resolve eq154150 eq43332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154150
  have eq154153 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq154152
       have r₂ := eq27
       grind)
    | exact resolve eq154152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154152
  have eq154186 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq154153 eq913
    | exact resolve eq913 eq154153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq154199 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq154153 eq43353
    | exact resolve eq43353 eq154153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43353 eq154153
  have eq158878 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq154186 eq154199
    | exact resolve eq154199 eq154186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154186 eq154199
  have eq158990 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by grind
  clear eq158878
  have eq158999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq43332 eq158990
    | exact resolve eq158990 eq43332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158990
  have eq159000 : x = y := by
    first
    | (have r₁ := eq158999
       have r₂ := eq27
       grind)
    | exact resolve eq158999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158999
  have eq159002 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq159000
       grind)
    | exact superpose eq159000 eq24
    | exact resolve eq24 eq159000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq159105 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43225
       have i₂ := eq159000
       grind)
    | exact superpose eq159000 eq43225
    | exact resolve eq43225 eq159000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43225
  have eq159264 : x = (M.op x x) := by
    first
    | (have j1 := eq3575 x
       grind)
    | (have r₁ := eq159105
       have r₂ := eq3575 x
       grind)
    | exact resolve eq159105 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575 eq159105
  have eq159361 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43295 eq159002
    | exact resolve eq159002 eq43295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43295 eq159002
  have eq159446 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq159361
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq159361
    | exact resolve eq159361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159361
  have eq159657 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq159446 eq43332
    | exact resolve eq43332 eq159446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43332
  have eq160509 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq159657 eq6697
    | exact resolve eq6697 eq159657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6697 eq159657
  have eq160698 : (k y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43137 eq160509
    | exact resolve eq160509 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43137 eq160509
  have eq160731 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq160698
       have i₂ := eq47522
       grind)
    | exact superpose eq47522 eq160698
    | exact resolve eq160698 eq47522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47522 eq160698
  have eq160759 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq160731
       have i₂ := eq159000
       grind)
    | exact superpose eq159000 eq160731
    | exact resolve eq160731 eq159000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159000 eq160731
  have eq160775 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq160759
       have i₂ := eq159264
       grind)
    | exact superpose eq159264 eq160759
    | exact resolve eq160759 eq159264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159264 eq160759
  have eq160789 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq160775 eq15
    | exact resolve eq15 eq160775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160775
  have eq161034 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq160789
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq160789
    | exact resolve eq160789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq160789
  have eq161097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq159446 eq161034
    | exact resolve eq161034 eq159446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159446 eq161034
  have eq161124 : False := by grind
  exact eq161124

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq554
    | exact resolve eq554 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq558 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq555
       have r₂ := eq27
       grind)
    | exact resolve eq555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq580 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq587 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq558 eq14
    | exact resolve eq14 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq834 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq587 sF3
       have i₂ := eq580 sF3
       grind)
    | exact superpose eq580 eq587
    | exact resolve eq587 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq856 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq834 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq834
       grind)
    | exact resolve eq13 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq857 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq857 eq118
    | exact resolve eq118 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq857
  have eq909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq904
  have eq915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq909
    | exact resolve eq909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq917 : y = (M.op y x) := by
    first
    | (have r₁ := eq915
       have r₂ := eq27
       grind)
    | exact resolve eq915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq931 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq14
    | exact resolve eq14 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq14
    | exact resolve eq14 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq931 x
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq931
    | exact resolve eq931 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq977 : y = (M.op y y) := by
    first
    | (have i₁ := eq932 y
       have i₂ := eq580 y
       grind)
    | exact superpose eq580 eq932
    | exact resolve eq932 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq932
  have eq989 : x = (M.op y x) := by
    first
    | (have i₁ := eq940
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq940
    | exact resolve eq940 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1001 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq977
       grind)
    | exact resolve eq13 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1002 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1003 : x = y := by
    first
    | (have i₁ := eq989
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq989
    | exact resolve eq989 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1015 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq18
    | exact resolve eq18 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1016 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq24
    | exact resolve eq24 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1032 : x = (M.op x x) := by
    first
    | (have i₁ := eq917
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq917
    | exact resolve eq917 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1045 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1016
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1016
    | exact resolve eq1016 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1046 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1045 eq26
    | exact resolve eq26 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1045
  have eq1096 : x = (M.op x y) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq1032
    | exact resolve eq1032 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1097 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1096 eq20
    | exact resolve eq20 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1126 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1097
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1097
    | exact resolve eq1097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1097
  have eq1168 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1126 eq1046
    | exact resolve eq1046 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1202 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1002 X0
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq1002
    | exact resolve eq1002 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002 eq1003
  have eq1205 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1202 x
       grind)
    | exact superpose eq1202 eq43
    | exact resolve eq43 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1202
  have eq1213 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq1205
    | exact resolve eq1205 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq1205
  have eq1219 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1126 eq1213
    | exact resolve eq1213 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq1213
  have eq1222 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1219
    | exact resolve eq1219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1219
  have eq1230 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1222 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1222
  have eq1231 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1230
  have eq1233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1168 eq1231
    | exact resolve eq1231 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq1231
  have eq1236 : False := by grind
  exact eq1236
