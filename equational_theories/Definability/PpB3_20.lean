import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq65 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq67 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq23
    | exact resolve eq23 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq72 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X0 X0) X0 X2
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq62
    | exact resolve eq62 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq80 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq80
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
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
  have eq589 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq608 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ X0)) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (σ X1) = (M.op X0 X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0 X2
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq989 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq589 y x
       grind)
    | exact superpose eq589 eq16
    | (have j1 := eq589 y x
       grind)
    | exact resolve eq16 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq589 X0 X0
       grind)
    | exact superpose eq589 eq67
    | (have j1 := eq589 X0 X0
       grind)
    | exact resolve eq67 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq589
  have eq1030 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1034 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1030 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1030
    | (have j0 := eq1030 X0
       grind)
    | exact resolve eq1030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1306 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq1034 (τ X0)
       grind)
    | exact superpose eq1034 eq19
    | (have j1 := eq1034 (τ X0)
       grind)
    | exact resolve eq19 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1308 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1306 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1306
    | (have j0 := eq1306 X0
       grind)
    | exact resolve eq1306 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1324 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1308 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1308
    | (have j0 := eq1308 X0
       grind)
    | exact resolve eq1308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1339 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1324 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1324
    | (have j0 := eq1324 X0
       grind)
    | exact resolve eq1324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq8045 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq989
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq989
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq989 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq8048 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8045
  have eq75045 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (σ X0)
       have i₂ := eq608 (σ X0) X0 X0
       grind)
    | exact superpose eq608 eq65
    | (have j1 := eq608 (σ X0) X0 x
       grind)
    | exact resolve eq65 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq608
  have eq75076 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75045
  have eq75088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75076 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75076
    | (have j0 := eq75076 X0
       grind)
    | exact resolve eq75076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75076
  have eq75392 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq75088 (τ X0)
       grind)
    | exact superpose eq75088 eq19
    | (have j1 := eq75088 (τ X0)
       grind)
    | exact resolve eq19 eq75088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq75088
  have eq75462 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq75392 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq75392
    | (have j0 := eq75392 X0
       grind)
    | exact resolve eq75392 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq75392
  have eq75510 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq75462 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75462
    | (have j0 := eq75462 X0
       grind)
    | exact resolve eq75462 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75462
  have eq75550 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75510 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75510
    | (have j0 := eq75510 X0
       grind)
    | exact resolve eq75510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75510
  have eq76108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1339 X0
       have i₂ := eq75550 X0
       grind)
    | exact superpose eq75550 eq1339
    | (have j0 := eq1339 X0
       have j1 := eq75550 X0
       grind)
    | exact resolve eq1339 eq75550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq75550
  have eq76357 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq76108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76108
  have eq76432 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76357 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq76357 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq76357 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76357
  have eq76834 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76432 (σ X0)
       grind)
    | exact superpose eq76432 eq15
    | exact resolve eq15 eq76432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76846 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq76432 (τ X0)
       grind)
    | exact superpose eq76432 eq32
    | exact resolve eq32 eq76432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq76953 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq76846 X0
       have i₂ := eq76432 X0
       grind)
    | exact superpose eq76432 eq76846
    | exact resolve eq76846 eq76432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76846
  have eq76965 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq76834 X0
       have i₂ := eq76432 X0
       grind)
    | exact superpose eq76432 eq76834
    | exact resolve eq76834 eq76432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76432 eq76834
  have eq77871 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 (τ X0) X1
       have i₂ := eq76953 X0
       grind)
    | exact superpose eq76953 eq80
    | exact resolve eq80 eq76953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76953
  have eq78259 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76965 x
       have i₂ := eq8048
       grind)
    | exact superpose eq8048 eq76965
    | exact resolve eq76965 eq8048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8048
  have eq78330 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq76965 X0
       grind)
    | exact superpose eq76965 eq9
    | exact resolve eq9 eq76965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78355 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0) (σ X0)
       have i₂ := eq76965 X0
       grind)
    | exact superpose eq76965 eq94
    | exact resolve eq94 eq76965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82339 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78330 (σ X0) X1
       have i₂ := eq76965 X0
       grind)
    | exact superpose eq76965 eq78330
    | exact resolve eq78330 eq76965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78330
  have eq1530907 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 (σ x) (σ y)
       have i₂ := eq78259
       grind)
    | exact superpose eq78259 eq94
    | exact resolve eq94 eq78259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78259
  have eq1531829 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1530907
       have i₂ := eq76965 x
       grind)
    | exact superpose eq76965 eq1530907
    | exact resolve eq1530907 eq76965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76965 eq1530907
  have eq1532041 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1531829
       grind)
    | exact superpose eq1531829 eq10
    | exact resolve eq10 eq1531829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531829
  have eq1532590 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1532041
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1532041
    | exact resolve eq1532041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532041
  have eq1532591 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1532590
  have eq1535237 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1532591
       grind)
    | exact superpose eq1532591 eq10
    | exact resolve eq10 eq1532591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532591
  have eq1535781 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1535237
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1535237
    | exact resolve eq1535237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535237
  have eq1536025 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78355 x
       have i₂ := eq1535781
       grind)
    | exact superpose eq1535781 eq78355
    | exact resolve eq78355 eq1535781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78355
  have eq1536292 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 x x
       have i₂ := eq1535781
       grind)
    | exact superpose eq1535781 eq94
    | exact resolve eq94 eq1535781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536920 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1535781
  have eq1544774 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1536025
       grind)
    | exact superpose eq1536025 eq16
    | exact resolve eq16 eq1536025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536025
  have eq1548241 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1544774
       have i₂ := eq1536292
       grind)
    | exact superpose eq1536292 eq1544774
    | exact resolve eq1544774 eq1536292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536292 eq1544774
  have eq1548250 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1548241
  have eq1548251 : x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1548250
  have eq1548252 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1548251
       have r₂ := eq1536920
       grind)
    | exact resolve eq1548251 eq1536920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536920 eq1548251
  have eq1548282 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94 x y
       have i₂ := eq1548252
       grind)
    | exact superpose eq1548252 eq94
    | exact resolve eq94 eq1548252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548252
  have eq1548902 : x = (M.op x x) := by grind
  clear eq1548282
  have eq1549254 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq80 x X0
       have i₂ := eq1548902
       grind)
    | exact superpose eq1548902 eq80
    | exact resolve eq80 eq1548902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1549305 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77871 x X0
       have i₂ := eq1548902
       grind)
    | exact superpose eq1548902 eq77871
    | exact resolve eq77871 eq1548902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77871
  have eq1549635 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq492 x x x
       have i₂ := eq1548902
       grind)
    | exact superpose eq1548902 eq492
    | exact resolve eq492 eq1548902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548902
  have eq1550510 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1549635 X0
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq1549635
    | exact resolve eq1549635 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1549635
  have eq1552432 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1549254 X0
       have i₂ := eq1550510 X0
       grind)
    | exact superpose eq1550510 eq1549254
    | exact resolve eq1549254 eq1550510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549254 eq1550510
  have eq1552979 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq492 x X1 X0
       have i₂ := eq1552432 X0
       grind)
    | exact superpose eq1552432 eq492
    | exact resolve eq492 eq1552432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq1555866 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1552979 X0 X0
       have i₂ := eq1552432 X0
       grind)
    | exact superpose eq1552432 eq1552979
    | exact resolve eq1552979 eq1552432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552979
  have eq1720996 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1549305 X0
       have i₂ := eq1555866 X0 (τ x)
       grind)
    | exact superpose eq1555866 eq1549305
    | exact resolve eq1549305 eq1555866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549305
  have eq1721263 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq82339 (τ x) X0
       have i₂ := eq1720996 (τ x)
       grind)
    | exact superpose eq1720996 eq82339
    | exact resolve eq82339 eq1720996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82339 eq1720996
  have eq1724089 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1721263 X0
       have i₂ := eq1555866 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq1555866 eq1721263
    | exact resolve eq1721263 eq1555866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555866 eq1721263
  have eq1724550 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1724089 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq1724089
    | exact resolve eq1724089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724089
  have eq1725211 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1724550 (σ y)
       grind)
    | exact superpose eq1724550 eq16
    | exact resolve eq16 eq1724550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724550
  have eq1728400 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1725211
       have i₂ := eq1552432 y
       grind)
    | exact superpose eq1552432 eq1725211
    | exact resolve eq1725211 eq1552432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552432 eq1725211
  have eq1728401 : False := by grind
  exact eq1728401

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq217 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq400 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq407 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq400 X0
       grind)
    | exact superpose eq400 eq14
    | exact resolve eq14 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq898 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq407
    | exact resolve eq407 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq60 eq407
    | exact resolve eq407 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq903 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq61 eq407
    | exact resolve eq407 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq407
  have eq8235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8235
    | exact resolve eq8235 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8235
  have eq8247 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8236
       have r₂ := eq28
       grind)
    | exact resolve eq8236 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8236
  have eq8249 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8247
    | exact resolve eq8247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247
  have eq8403 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8249 eq70
    | exact resolve eq70 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8422 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8249 eq898
    | exact resolve eq898 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8249
  have eq8423 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8422
    | exact resolve eq8422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8425 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8403
       have r₂ := eq52
       grind)
    | exact resolve eq8403 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8403
  have eq8431 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8425 eq101
    | exact resolve eq101 eq8425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq8425
  have eq8439 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8431
  have eq8677 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq898 x x
       have i₂ := eq8439
       grind)
    | exact superpose eq8439 eq898
    | exact resolve eq898 eq8439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq8678 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8677
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8677
    | exact resolve eq8677 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8677
  have eq8731 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8678 eq30
    | exact resolve eq30 eq8678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8678
  have eq8855 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq8731
    | exact resolve eq8731 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq8731
  have eq8856 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8855
  have eq8857 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8856 eq21
    | exact resolve eq21 eq8856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8856
  have eq8994 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8857
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8857
    | exact resolve eq8857 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857
  have eq34656 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq8423
       grind)
    | exact superpose eq8423 eq70
    | exact resolve eq70 eq8423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq8423
  have eq34713 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34656
       have r₂ := eq51
       grind)
    | exact resolve eq34656 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq34656
  have eq34719 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq34713
       grind)
    | exact superpose eq34713 eq76
    | exact resolve eq76 eq34713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq34713
  have eq34759 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34719
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34719
    | exact resolve eq34719 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34719
  have eq34771 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34759
       have r₂ := eq52
       grind)
    | exact resolve eq34759 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq34759
  have eq34856 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34771 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq34771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34771
  have eq34866 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq34856
    | exact resolve eq34856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34856
  have eq34867 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34866
  have eq34881 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq34867
    | exact resolve eq34867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34867
  have eq35608 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34881 eq898
    | exact resolve eq898 eq34881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq34881
  have eq35613 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35608
    | exact resolve eq35608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35608
  have eq35614 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35613
  have eq35616 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35614 eq28
    | exact resolve eq28 eq35614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35614
  have eq35661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8994 eq35616
    | (have r₁ := eq35616
       have r₂ := eq8994
       grind)
    | exact resolve eq35616 eq8994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35664 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35661
  have eq35672 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35664 eq217
    | exact resolve eq217 eq35664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq35702 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35664 eq903
    | exact resolve eq903 eq35664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq35664
  have eq36313 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35702 eq35672
    | exact resolve eq35672 eq35702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35672 eq35702
  have eq36373 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36313
  have eq36375 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq36373
    | exact resolve eq36373 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36373
  have eq36690 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36375 eq28
    | exact resolve eq28 eq36375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36375
  have eq36746 : x = (M.op x y) := by
    first
    | (have r₁ := eq36690
       have r₂ := eq8994
       grind)
    | exact resolve eq36690 eq8994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8994 eq36690
  have eq36748 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq36746 eq21
    | exact resolve eq21 eq36746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq36843 : x = (M.op x x) := by
    first
    | exact superpose eq36746 eq901
    | exact resolve eq901 eq36746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq36931 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq36748
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36748
    | exact resolve eq36748 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36748
  have eq37592 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq36843
       grind)
    | exact superpose eq36843 eq57
    | exact resolve eq57 eq36843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq37715 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq36746 eq37592
    | exact resolve eq37592 eq36746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37592
  have eq37742 : y = (M.op x y) := by
    first
    | (have i₁ := eq37715
       have i₂ := eq36843
       grind)
    | exact superpose eq36843 eq37715
    | exact resolve eq37715 eq36843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36843 eq37715
  have eq37752 : y = (M.op x y) := by
    first
    | (have i₁ := eq37742
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37742
    | exact resolve eq37742 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq37742
  have eq37759 : x = y := by
    first
    | exact superpose eq36746 eq37752
    | exact resolve eq37752 eq36746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36746 eq37752
  have eq37763 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq37759
       grind)
    | exact superpose eq37759 eq25
    | exact resolve eq25 eq37759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq37759
  have eq37965 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37763
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37763
    | exact resolve eq37763 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37763
  have eq38042 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq36931 eq37965
    | exact resolve eq37965 eq36931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37965
  have eq38193 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38042 eq35616
    | (have r₁ := eq35616
       have r₂ := eq38042
       grind)
    | exact resolve eq35616 eq38042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35616 eq38042
  have eq38196 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38193
  have eq38198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36931 eq38196
    | exact resolve eq38196 eq36931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36931 eq38196
  have eq38270 : False := by grind
  exact eq38270

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = X1 ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X1
       have i₂ := eq14 X2 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq86 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq171 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq96
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq226 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq9
    | exact resolve eq9 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X2 X3
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq24
    | exact resolve eq24 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq388 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq16
    | (have j1 := eq60 x x
       grind)
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq639 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op X0 X2) X0 X2
       have i₂ := eq59 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq59 eq33
    | (have j1 := eq59 X0 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq33 (M.op X0 X2) X0 X2
       have r₂ := eq59 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq33 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq59
  have eq641 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq639 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq642 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq641 X0 X1 X2
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq641
    | (have j0 := eq641 X0 X1 X2
       grind)
    | exact resolve eq641 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq642 X0 X1 X2
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq642
    | (have j0 := eq642 X0 X1 X2
       grind)
    | exact resolve eq642 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq7467 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq388
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq388
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq388 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq388
  have eq7468 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq7467
  have eq23389 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq645 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq23390 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq23389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23389
  have eq23412 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq23390 X0 X1
       have j1 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq23390 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq23390 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23390
  have eq23481 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23412 (M.op (M.op (M.op (M.op X0 x) (M.op X0 x)) x) (M.op X0 x)) x
       have i₂ := eq231 X0 x x x
       grind)
    | exact superpose eq231 eq23412
    | exact resolve eq23412 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq23412
  have eq24095 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23481 (σ X0)
       grind)
    | exact superpose eq23481 eq15
    | exact resolve eq15 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq23481 (τ X0)
       grind)
    | exact superpose eq23481 eq34
    | exact resolve eq34 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq24134 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24103 X0
       have i₂ := eq23481 X0
       grind)
    | exact superpose eq23481 eq24103
    | exact resolve eq24103 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24103
  have eq24140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24095 X0
       have i₂ := eq23481 X0
       grind)
    | exact superpose eq23481 eq24095
    | exact resolve eq24095 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24095
  have eq24472 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq24134 X0
       grind)
    | exact superpose eq24134 eq9
    | exact resolve eq9 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24134
  have eq24936 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq24140 X0
       grind)
    | exact superpose eq24140 eq9
    | exact resolve eq9 eq24140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34528 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24936 (σ X0) X1
       have i₂ := eq24140 X0
       grind)
    | exact superpose eq24140 eq24936
    | exact resolve eq24936 eq24140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24936
  have eq147549 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq171 (σ x) (σ y)
       have i₂ := eq7468
       grind)
    | exact superpose eq7468 eq171
    | exact resolve eq171 eq7468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7468
  have eq147637 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq147549
  have eq147686 : (σ x) = (σ (M.op x x)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147637
       have i₂ := eq24140 x
       grind)
    | exact superpose eq24140 eq147637
    | exact resolve eq147637 eq24140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24140 eq147637
  have eq147792 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147686
       have i₂ := eq23481 x
       grind)
    | exact superpose eq23481 eq147686
    | exact resolve eq147686 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481 eq147686
  have eq163711 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq147792
       grind)
    | exact superpose eq147792 eq10
    | exact resolve eq10 eq147792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147792
  have eq163890 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163711
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq163711
    | exact resolve eq163711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163711
  have eq163891 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq163890
  have eq165086 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq171 x y
       have i₂ := eq163891
       grind)
    | exact superpose eq163891 eq171
    | exact resolve eq171 eq163891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163891
  have eq165171 : x = (M.op x x) := by grind
  clear eq165086
  have eq166316 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24472 x X0
       have i₂ := eq165171
       grind)
    | exact superpose eq165171 eq24472
    | exact resolve eq24472 eq165171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24472
  have eq166386 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq165171
       grind)
    | exact superpose eq165171 eq9
    | exact resolve eq9 eq165171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166467 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq226 x x x
       have i₂ := eq165171
       grind)
    | exact superpose eq165171 eq226
    | exact resolve eq226 eq165171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165171
  have eq166561 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq166467 X0
       have i₂ := eq171 x X0
       grind)
    | exact superpose eq171 eq166467
    | exact resolve eq166467 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq166467
  have eq169147 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq166386 X0
       have i₂ := eq166561 X0
       grind)
    | exact superpose eq166561 eq166386
    | exact resolve eq166386 eq166561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169320 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq166386 X0
       grind)
    | exact superpose eq166386 eq226
    | exact resolve eq226 eq166386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq166386
  have eq169475 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169320 X0 X1
       have i₂ := eq166561 X0
       grind)
    | exact superpose eq166561 eq169320
    | exact resolve eq169320 eq166561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166561 eq169320
  have eq169570 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq169475 X0 X0
       have i₂ := eq169147 X0
       grind)
    | exact superpose eq169147 eq169475
    | exact resolve eq169475 eq169147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169475
  have eq195482 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq166316 X0
       have i₂ := eq169570 X0 (τ x)
       grind)
    | exact superpose eq169570 eq166316
    | exact resolve eq166316 eq169570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166316
  have eq197074 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34528 (τ x) X0
       have i₂ := eq195482 (τ x)
       grind)
    | exact superpose eq195482 eq34528
    | exact resolve eq34528 eq195482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34528 eq195482
  have eq197536 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq197074 X0
       have i₂ := eq169570 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq169570 eq197074
    | exact resolve eq197074 eq169570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169570 eq197074
  have eq197626 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq197536 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq197536
    | exact resolve eq197536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197536
  have eq198465 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197626 (σ y)
       grind)
    | exact superpose eq197626 eq16
    | exact resolve eq16 eq197626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197626
  have eq199023 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq198465
       have i₂ := eq169147 y
       grind)
    | exact superpose eq169147 eq198465
    | exact resolve eq198465 eq169147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169147 eq198465
  have eq199024 : False := by grind
  exact eq199024

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq177 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq177 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq178 (σ X0)
       grind)
    | exact superpose eq178 eq15
    | exact resolve eq15 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq181
    | exact resolve eq181 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq97
    | exact resolve eq97 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq297
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq297
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq297
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq297
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq297 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq3075 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3074
  have eq28463 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3075
       grind)
    | exact superpose eq3075 eq16
    | exact resolve eq16 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq28464 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28463
       have r₂ := eq192 x
       grind)
    | exact resolve eq28463 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28463
  have eq28512 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131 x y
       have i₂ := eq28464
       grind)
    | exact superpose eq28464 eq131
    | exact resolve eq131 eq28464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28464
  have eq28563 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28512
       grind)
    | exact superpose eq28512 eq10
    | exact resolve eq10 eq28512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28512
  have eq28670 : x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28563
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28563
    | exact resolve eq28563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28563
  have eq28693 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28670
       grind)
    | exact superpose eq28670 eq16
    | exact resolve eq16 eq28670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28670
  have eq28694 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28693
       have r₂ := eq192 x
       grind)
    | exact resolve eq28693 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28693
  have eq28767 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq131 (σ x) (σ y)
       have i₂ := eq28694
       grind)
    | exact superpose eq28694 eq131
    | exact resolve eq131 eq28694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28694
  have eq28794 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28767
       have i₂ := eq192 x
       grind)
    | exact superpose eq192 eq28767
    | exact resolve eq28767 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq28767
  have eq29270 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq28794
       grind)
    | exact superpose eq28794 eq10
    | exact resolve eq10 eq28794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28794
  have eq29378 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29270
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29270
    | exact resolve eq29270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29270
  have eq29379 : x = (M.op x x) := by grind
  clear eq29378
  have eq29855 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 x X0
       have i₂ := eq29379
       grind)
    | exact superpose eq29379 eq217
    | exact resolve eq217 eq29379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq29913 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq29379
       grind)
    | exact superpose eq29379 eq9
    | exact resolve eq9 eq29379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29960 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq150 x x x
       have i₂ := eq29379
       grind)
    | exact superpose eq29379 eq150
    | exact resolve eq150 eq29379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29379
  have eq29987 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq29960 X0
       have i₂ := eq131 x X0
       grind)
    | exact superpose eq131 eq29960
    | exact resolve eq29960 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq29960
  have eq30332 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29913 X0
       have i₂ := eq29987 X0
       grind)
    | exact superpose eq29987 eq29913
    | exact resolve eq29913 eq29987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30411 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq29913 X0
       grind)
    | exact superpose eq29913 eq150
    | exact resolve eq150 eq29913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq29913
  have eq30447 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30411 X0 X1
       have i₂ := eq29987 X0
       grind)
    | exact superpose eq29987 eq30411
    | exact resolve eq30411 eq29987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29987 eq30411
  have eq30487 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30447 X0 X0
       have i₂ := eq30332 X0
       grind)
    | exact superpose eq30332 eq30447
    | exact resolve eq30447 eq30332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30447
  have eq35248 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29855 X0
       have i₂ := eq30487 X0 (σ x)
       grind)
    | exact superpose eq30487 eq29855
    | exact resolve eq29855 eq30487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29855 eq30487
  have eq35824 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35248 (σ y)
       grind)
    | exact superpose eq35248 eq16
    | exact resolve eq16 eq35248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35248
  have eq36100 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq35824
       have i₂ := eq30332 y
       grind)
    | exact superpose eq30332 eq35824
    | exact resolve eq35824 eq30332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30332 eq35824
  have eq36101 : False := by grind
  exact eq36101

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq177 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq177 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq178 (σ X0)
       grind)
    | exact superpose eq178 eq15
    | exact resolve eq15 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq181
    | exact resolve eq181 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq97
    | exact resolve eq97 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq297
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq297
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq297
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq297
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq297 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq3075 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3074
  have eq28463 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3075
       grind)
    | exact superpose eq3075 eq16
    | exact resolve eq16 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq28464 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28463
       have r₂ := eq192 x
       grind)
    | exact resolve eq28463 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28463
  have eq28512 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131 x y
       have i₂ := eq28464
       grind)
    | exact superpose eq28464 eq131
    | exact resolve eq131 eq28464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28464
  have eq28563 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28512
       grind)
    | exact superpose eq28512 eq10
    | exact resolve eq10 eq28512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28512
  have eq28670 : x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28563
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28563
    | exact resolve eq28563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28563
  have eq28693 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28670
       grind)
    | exact superpose eq28670 eq16
    | exact resolve eq16 eq28670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28670
  have eq28694 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28693
       have r₂ := eq192 x
       grind)
    | exact resolve eq28693 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28693
  have eq28767 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq131 (σ x) (σ y)
       have i₂ := eq28694
       grind)
    | exact superpose eq28694 eq131
    | exact resolve eq131 eq28694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28694
  have eq28794 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28767
       have i₂ := eq192 x
       grind)
    | exact superpose eq192 eq28767
    | exact resolve eq28767 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq28767
  have eq29270 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq28794
       grind)
    | exact superpose eq28794 eq10
    | exact resolve eq10 eq28794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28794
  have eq29378 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29270
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29270
    | exact resolve eq29270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29270
  have eq29379 : x = (M.op x x) := by grind
  clear eq29378
  have eq29855 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 x X0
       have i₂ := eq29379
       grind)
    | exact superpose eq29379 eq217
    | exact resolve eq217 eq29379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq29913 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq29379
       grind)
    | exact superpose eq29379 eq9
    | exact resolve eq9 eq29379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29960 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq150 x x x
       have i₂ := eq29379
       grind)
    | exact superpose eq29379 eq150
    | exact resolve eq150 eq29379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29379
  have eq29987 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq29960 X0
       have i₂ := eq131 x X0
       grind)
    | exact superpose eq131 eq29960
    | exact resolve eq29960 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq29960
  have eq30332 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29913 X0
       have i₂ := eq29987 X0
       grind)
    | exact superpose eq29987 eq29913
    | exact resolve eq29913 eq29987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30411 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq29913 X0
       grind)
    | exact superpose eq29913 eq150
    | exact resolve eq150 eq29913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq29913
  have eq30447 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30411 X0 X1
       have i₂ := eq29987 X0
       grind)
    | exact superpose eq29987 eq30411
    | exact resolve eq30411 eq29987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29987 eq30411
  have eq30487 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30447 X0 X0
       have i₂ := eq30332 X0
       grind)
    | exact superpose eq30332 eq30447
    | exact resolve eq30447 eq30332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30447
  have eq35248 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29855 X0
       have i₂ := eq30487 X0 (σ x)
       grind)
    | exact superpose eq30487 eq29855
    | exact resolve eq29855 eq30487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29855 eq30487
  have eq35824 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35248 (σ y)
       grind)
    | exact superpose eq35248 eq16
    | exact resolve eq16 eq35248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35248
  have eq36100 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq35824
       have i₂ := eq30332 y
       grind)
    | exact superpose eq30332 eq35824
    | exact resolve eq35824 eq30332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30332 eq35824
  have eq36101 : False := by grind
  exact eq36101

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq177 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq177 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq178 (σ X0)
       grind)
    | exact superpose eq178 eq15
    | exact resolve eq15 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq181
    | exact resolve eq181 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq97
    | exact resolve eq97 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq228 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq228
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq228
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq228
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq228
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq228 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq3045 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3044
  have eq28648 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3045
       grind)
    | exact superpose eq3045 eq16
    | exact resolve eq16 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq28649 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28648
       have r₂ := eq192 x
       grind)
    | exact resolve eq28648 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28648
  have eq28696 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131 x y
       have i₂ := eq28649
       grind)
    | exact superpose eq28649 eq131
    | exact resolve eq131 eq28649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28649
  have eq28749 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28696
       grind)
    | exact superpose eq28696 eq10
    | exact resolve eq10 eq28696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28696
  have eq28852 : x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28749
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28749
    | exact resolve eq28749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28749
  have eq29257 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28852
       grind)
    | exact superpose eq28852 eq16
    | exact resolve eq16 eq28852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28852
  have eq29258 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29257
       have r₂ := eq192 x
       grind)
    | exact resolve eq29257 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29257
  have eq29330 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq131 (σ x) (σ y)
       have i₂ := eq29258
       grind)
    | exact superpose eq29258 eq131
    | exact resolve eq131 eq29258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29258
  have eq29359 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29330
       have i₂ := eq192 x
       grind)
    | exact superpose eq192 eq29330
    | exact resolve eq29330 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq29330
  have eq29859 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29359
       grind)
    | exact superpose eq29359 eq10
    | exact resolve eq10 eq29359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29359
  have eq29964 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29859
    | exact resolve eq29859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29859
  have eq29965 : x = (M.op x x) := by grind
  clear eq29964
  have eq30147 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 x X0
       have i₂ := eq29965
       grind)
    | exact superpose eq29965 eq217
    | exact resolve eq217 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq30210 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq29965
       grind)
    | exact superpose eq29965 eq9
    | exact resolve eq9 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30256 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq150 x x x
       have i₂ := eq29965
       grind)
    | exact superpose eq29965 eq150
    | exact resolve eq150 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29965
  have eq30288 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq30256 X0
       have i₂ := eq131 x X0
       grind)
    | exact superpose eq131 eq30256
    | exact resolve eq30256 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq30256
  have eq30654 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30210 X0
       have i₂ := eq30288 X0
       grind)
    | exact superpose eq30288 eq30210
    | exact resolve eq30210 eq30288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30730 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq30210 X0
       grind)
    | exact superpose eq30210 eq150
    | exact resolve eq150 eq30210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq30210
  have eq30766 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30730 X0 X1
       have i₂ := eq30288 X0
       grind)
    | exact superpose eq30288 eq30730
    | exact resolve eq30730 eq30288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30288 eq30730
  have eq30809 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30766 X0 X0
       have i₂ := eq30654 X0
       grind)
    | exact superpose eq30654 eq30766
    | exact resolve eq30766 eq30654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30766
  have eq35924 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30147 X0
       have i₂ := eq30809 X0 (σ x)
       grind)
    | exact superpose eq30809 eq30147
    | exact resolve eq30147 eq30809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30147 eq30809
  have eq36170 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35924 (σ y)
       grind)
    | exact superpose eq35924 eq16
    | exact resolve eq16 eq35924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35924
  have eq36460 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq36170
       have i₂ := eq30654 y
       grind)
    | exact superpose eq30654 eq36170
    | exact resolve eq36170 eq30654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30654 eq36170
  have eq36461 : False := by grind
  exact eq36461

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq9
    | exact resolve eq9 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq177 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq177 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq177 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq178 (σ X0)
       grind)
    | exact superpose eq178 eq15
    | exact resolve eq15 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq181
    | exact resolve eq181 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq97
    | exact resolve eq97 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq295 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq295
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq295
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq295
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq295
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq295 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq2873 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2872
  have eq30489 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2873
       grind)
    | exact superpose eq2873 eq16
    | exact resolve eq16 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq30490 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30489
       have r₂ := eq192 x
       grind)
    | exact resolve eq30489 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30489
  have eq30538 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131 x y
       have i₂ := eq30490
       grind)
    | exact superpose eq30490 eq131
    | exact resolve eq131 eq30490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30490
  have eq30601 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30538
       grind)
    | exact superpose eq30538 eq10
    | exact resolve eq10 eq30538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30538
  have eq30707 : x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30601
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30601
    | exact resolve eq30601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30601
  have eq31151 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30707
       grind)
    | exact superpose eq30707 eq16
    | exact resolve eq16 eq30707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30707
  have eq31152 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq31151
       have r₂ := eq192 x
       grind)
    | exact resolve eq31151 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31151
  have eq31229 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq131 (σ x) (σ y)
       have i₂ := eq31152
       grind)
    | exact superpose eq31152 eq131
    | exact resolve eq131 eq31152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31152
  have eq31269 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31229
       have i₂ := eq192 x
       grind)
    | exact superpose eq192 eq31229
    | exact resolve eq31229 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq31229
  have eq35279 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq31269
       grind)
    | exact superpose eq31269 eq10
    | exact resolve eq10 eq31269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31269
  have eq35392 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35279
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35279
    | exact resolve eq35279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35279
  have eq35393 : x = (M.op x x) := by grind
  clear eq35392
  have eq35423 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 x X0
       have i₂ := eq35393
       grind)
    | exact superpose eq35393 eq217
    | exact resolve eq217 eq35393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq35509 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq35393
       grind)
    | exact superpose eq35393 eq9
    | exact resolve eq9 eq35393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35556 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq150 x x x
       have i₂ := eq35393
       grind)
    | exact superpose eq35393 eq150
    | exact resolve eq150 eq35393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35393
  have eq35599 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq35556 X0
       have i₂ := eq131 x X0
       grind)
    | exact superpose eq131 eq35556
    | exact resolve eq35556 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq35556
  have eq36615 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35509 X0
       have i₂ := eq35599 X0
       grind)
    | exact superpose eq35599 eq35509
    | exact resolve eq35509 eq35599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36711 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X1) = (M.op (M.op (M.op (M.op (M.op x X0) x) X1) X0) (M.op (M.op (M.op x X0) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (M.op (M.op x X0) x) X1 X0
       have i₂ := eq35509 X0
       grind)
    | exact superpose eq35509 eq150
    | exact resolve eq150 eq35509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq35509
  have eq36778 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36711 X0 X1
       have i₂ := eq35599 X0
       grind)
    | exact superpose eq35599 eq36711
    | exact resolve eq36711 eq35599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35599 eq36711
  have eq36838 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36778 X0 X0
       have i₂ := eq36615 X0
       grind)
    | exact superpose eq36615 eq36778
    | exact resolve eq36778 eq36615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36778
  have eq49721 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35423 X0
       have i₂ := eq36838 X0 (σ x)
       grind)
    | exact superpose eq36838 eq35423
    | exact resolve eq35423 eq36838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35423 eq36838
  have eq50509 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49721 (σ y)
       grind)
    | exact superpose eq49721 eq16
    | exact resolve eq16 eq49721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49721
  have eq50878 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq50509
       have i₂ := eq36615 y
       grind)
    | exact superpose eq36615 eq50509
    | exact resolve eq50509 eq36615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36615 eq50509
  have eq50879 : False := by grind
  exact eq50879

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq100 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq9
    | exact resolve eq9 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq100
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq166 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq84 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq173 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq174 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq174
    | (have j0 := eq174 X0 X1
       grind)
    | exact resolve eq174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       have j1 := eq172 X1 X0
       grind)
    | (have r₁ := eq176 X1 X0
       have r₂ := eq172 X0 X1
       grind)
    | (have r₁ := eq176 (k X1 X0) X1
       have r₂ := eq172 X0 X1
       grind)
    | (have r₁ := eq176 X1 X1
       have r₂ := eq172 X1 X1
       grind)
    | exact resolve eq176 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq176
  have eq443 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq134 (τ X0) (τ X0)
       grind)
    | exact superpose eq134 eq34
    | exact resolve eq34 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq798 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 y x
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 y x
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq842 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq798
    | (have j0 := eq798 X0 X1
       grind)
    | exact resolve eq798 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq798
  have eq1056 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq842
    | exact resolve eq842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1117 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1056 (τ X1) X0
       grind)
    | exact superpose eq1056 eq18
    | (have j1 := eq1056 (τ X1) X0
       grind)
    | exact resolve eq18 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1505 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq443 (σ X0)
       grind)
    | exact superpose eq443 eq25
    | exact resolve eq25 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq1511 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq1505 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq1505
    | exact resolve eq1505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1532 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1511 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1511
    | exact resolve eq1511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1570 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1532 (σ X0)
       grind)
    | exact superpose eq1532 eq25
    | exact resolve eq25 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1532
  have eq2105 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1117 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1117
    | exact resolve eq1117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq2193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2105 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2105
    | (have j0 := eq2105 X0 X1
       grind)
    | exact resolve eq2105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq812
       have i₂ := eq2193 y x
       grind)
    | exact superpose eq2193 eq812
    | (have j1 := eq2193 (σ y) (σ x)
       grind)
    | (have r₁ := eq812
       have r₂ := eq2193 y x
       grind)
    | exact resolve eq812 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2375 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2374
  have eq2505 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2375
  have eq2913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq812
       have i₂ := eq2505
       grind)
    | exact superpose eq2505 eq812
    | exact resolve eq812 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq2505
  have eq2914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2913
  have eq2915 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2914
  have eq2921 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq1570 x
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq1570
    | exact resolve eq1570 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq2969 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq134 (σ x) (σ x)
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq134
    | exact resolve eq134 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq2982 : y = (k y x) := by
    first
    | (have i₁ := eq2921
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2921
    | exact resolve eq2921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq3134 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1056 y x
       have i₂ := eq2982
       grind)
    | exact superpose eq2982 eq1056
    | (have j0 := eq1056 y x
       grind)
    | exact resolve eq1056 eq2982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq2982
  have eq3398 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2969
       grind)
    | exact superpose eq2969 eq16
    | exact resolve eq16 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq3604 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3398
       have i₂ := eq3134
       grind)
    | exact superpose eq3134 eq3398
    | exact resolve eq3398 eq3134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134
  have eq3644 : y = (M.op x x) := by grind
  clear eq3604
  have eq3692 : y = (M.op x y) := by
    first
    | (have i₁ := eq134 x x
       have i₂ := eq3644
       grind)
    | exact superpose eq3644 eq134
    | exact resolve eq134 eq3644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq3644
  have eq3794 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3398
       have i₂ := eq3692
       grind)
    | exact superpose eq3692 eq3398
    | exact resolve eq3398 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398 eq3692
  have eq3834 : False := by grind
  exact eq3834
