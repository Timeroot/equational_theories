import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k (M.op (M.op X0 X1) X1) (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) ∨ (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X1) (M.op X2 (M.op X0 X1))
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X1) (M.op X2 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq78 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq187 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3322 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq74 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3323 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3326 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3323 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3323
    | (have j0 := eq3323 X0
       grind)
    | exact resolve eq3323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq3332 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3326 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3326
    | exact resolve eq3326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq3366 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3332 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3332
    | (have j0 := eq3332 X0
       grind)
    | exact resolve eq3332 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq3368 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3366 X0
       grind)
    | exact superpose eq3366 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3366 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3366 X0
       grind)
    | exact resolve eq12 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq3383 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3368 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3368
  have eq3393 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3430 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3393 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq3393
    | (have j0 := eq3393 X0 X0
       grind)
    | exact resolve eq3393 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393
  have eq3447 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3383 X0 X1
       grind)
    | exact superpose eq3383 eq11
    | (have j1 := eq3383 X0 X1
       grind)
    | exact resolve eq11 eq3383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383
  have eq3554 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3447 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3447
    | (have j0 := eq3447 X0 X0
       grind)
    | exact resolve eq3447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq3638 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3554 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq3639 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq3799 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0 X0
       have i₂ := eq3639 X0
       grind)
    | exact superpose eq3639 eq187
    | (have j0 := eq187 X0 X0
       grind)
    | exact resolve eq187 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq3825 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3639 (σ X0)
       grind)
    | exact superpose eq3639 eq15
    | exact resolve eq15 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3858 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799
  have eq3891 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3825 X0
       have i₂ := eq3639 X0
       grind)
    | exact superpose eq3639 eq3825
    | exact resolve eq3825 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639 eq3825
  have eq4189 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq3891 X0
       grind)
    | exact superpose eq3891 eq9
    | exact resolve eq9 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4190 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq3891 X0
       grind)
    | exact superpose eq3891 eq9
    | exact resolve eq9 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4635 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4189 (M.op X0 X0) (M.op (σ X0) (M.op (σ X0) x))
       have i₂ := eq4189 X0 x
       grind)
    | exact superpose eq4189 eq4189
    | exact resolve eq4189 eq4189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6041 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3430 X0 X2
       grind)
    | exact superpose eq3430 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3430 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3430 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3430 X1 X1
       grind)
    | exact resolve eq12 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3430
  have eq6079 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq6041 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041
  have eq13670 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq6079 X0 X2 X1
       grind)
    | exact superpose eq6079 eq11
    | (have j1 := eq6079 X0 X2 X1
       grind)
    | exact resolve eq11 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079
  have eq13811 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13670 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq13670
    | (have j0 := eq13670 X0 X1 X1
       grind)
    | exact resolve eq13670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13670
  have eq13982 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13811 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13811
  have eq13983 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13982 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13982
  have eq14237 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq13983 X1 (τ X0)
       grind)
    | exact superpose eq13983 eq18
    | (have j1 := eq13983 X1 (τ X0)
       grind)
    | exact resolve eq18 eq13983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13983 (σ X1) (σ X0)
       grind)
    | exact superpose eq13983 eq15
    | (have j1 := eq13983 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq13983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13983
  have eq14868 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14237 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14237
    | exact resolve eq14237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14237
  have eq15012 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14868 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14868
    | (have j0 := eq14868 X0 X1
       grind)
    | exact resolve eq14868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14868
  have eq16039 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14273 x y
       grind)
    | exact superpose eq14273 eq16
    | (have j1 := eq14273 x y
       grind)
    | exact resolve eq16 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16102 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14273
  have eq16219 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16102 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq16102
    | (have j0 := eq16102 (τ X1) (τ X0)
       grind)
    | exact resolve eq16102 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq16274 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16219 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq16219
    | (have j0 := eq16219 X0 X1
       grind)
    | exact resolve eq16219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16219
  have eq16302 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16274 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16274
    | (have j0 := eq16274 X0 X1
       grind)
    | exact resolve eq16274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16274
  have eq16320 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16302 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16302
    | (have j0 := eq16302 X0 X1
       grind)
    | exact resolve eq16302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16302
  have eq16333 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16320 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq16320
    | (have j0 := eq16320 X0 X1
       grind)
    | exact resolve eq16320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16320
  have eq17177 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16039
       have i₂ := eq15012 x y
       grind)
    | exact superpose eq15012 eq16039
    | (have j1 := eq15012 (σ x) (σ y)
       grind)
    | (have r₁ := eq16039
       have r₂ := eq15012 x y
       grind)
    | exact resolve eq16039 eq15012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15012
  have eq17180 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17177
  have eq17185 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq17180
       grind)
    | exact superpose eq17180 eq9
    | exact resolve eq9 eq17180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17186 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq17180
       grind)
    | exact superpose eq17180 eq9
    | exact resolve eq9 eq17180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17505 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ y = (M.op y (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq4190 y (σ x)
       have i₂ := eq17185 X0
       grind)
    | exact superpose eq17185 eq4190
    | (have j1 := eq17185 X0
       grind)
    | exact resolve eq4190 eq17185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17185
  have eq17691 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17186 X0
       have i₂ := eq17180
       grind)
    | exact superpose eq17180 eq17186
    | exact resolve eq17186 eq17180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17180 eq17186
  have eq17708 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17691
  have eq93955 : ∀ X0 : G, y = (M.op y (M.op y (M.op y X0))) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4189 y (σ (M.op y y))
       have i₂ := eq17505 X0
       grind)
    | exact superpose eq17505 eq4189
    | (have j1 := eq17505 X0
       grind)
    | exact resolve eq4189 eq17505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17505
  have eq94460 : y = (M.op y y) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq93955 (M.op y x)
       have i₂ := eq93955 x
       grind)
    | exact superpose eq93955 eq93955
    | exact resolve eq93955 eq93955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93955
  have eq94507 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq94460
  have eq94534 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4190 y (σ (M.op y y))
       have i₂ := eq94507
       grind)
    | exact superpose eq94507 eq4190
    | exact resolve eq4190 eq94507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190 eq94507
  have eq95342 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4189 y (M.op (σ y) (σ (M.op y y)))
       have i₂ := eq94534
       grind)
    | exact superpose eq94534 eq4189
    | exact resolve eq4189 eq94534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95352 : ∀ X0 : G, y = (M.op y y) ∨ (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ (M.op y y))
       have i₂ := eq94534
       grind)
    | exact superpose eq94534 eq9
    | exact resolve eq9 eq94534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94534
  have eq95421 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq95342
       have i₂ := eq3891 y
       grind)
    | exact superpose eq3891 eq95342
    | exact resolve eq95342 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95342
  have eq95444 : y = (M.op y y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq95421
       have i₂ := eq3891 (M.op y y)
       grind)
    | exact superpose eq3891 eq95421
    | exact resolve eq95421 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95421
  have eq95805 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3858 y
       have i₂ := eq95352 X0
       grind)
    | exact superpose eq95352 eq3858
    | (have j0 := eq3858 y
       have j1 := eq95352 X0
       grind)
    | exact resolve eq3858 eq95352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95352
  have eq95859 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq95805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95805
  have eq95883 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq95859 X0
       have i₂ := eq3891 y
       grind)
    | exact superpose eq3891 eq95859
    | (have j0 := eq95859 X0
       grind)
    | exact resolve eq95859 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95859
  have eq95930 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq4635 y
       have i₂ := eq95444
       grind)
    | exact superpose eq95444 eq4635
    | exact resolve eq4635 eq95444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4635 eq95444
  have eq95986 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq95930
       have i₂ := eq3891 y
       grind)
    | exact superpose eq3891 eq95930
    | exact resolve eq95930 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95930
  have eq96004 : (σ y) = (σ (M.op (M.op y y) (M.op y y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq95986
       have i₂ := eq3891 (M.op y y)
       grind)
    | exact superpose eq3891 eq95986
    | exact resolve eq95986 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95986
  have eq96005 : (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by grind
  clear eq96004
  have eq96839 : (M.op (M.op y y) (M.op y y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (M.op y y) (M.op y y))
       have i₂ := eq96005
       grind)
    | exact superpose eq96005 eq10
    | exact resolve eq10 eq96005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96005
  have eq97142 : y = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq96839
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq96839
    | exact resolve eq96839 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96839
  have eq105582 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95883 (M.op x (σ y))
       have i₂ := eq95883 x
       grind)
    | exact superpose eq95883 eq95883
    | exact resolve eq95883 eq95883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95883
  have eq105675 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq105582
  have eq105728 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq3858 y
       grind)
    | (have r₁ := eq105675
       have r₂ := eq3858 y
       grind)
    | exact resolve eq105675 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105675
  have eq105762 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105728
       have i₂ := eq3891 y
       grind)
    | exact superpose eq3891 eq105728
    | exact resolve eq105728 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105728
  have eq106538 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq105762
       grind)
    | exact superpose eq105762 eq10
    | exact resolve eq10 eq105762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106903 : y = (M.op y y) := by
    first
    | (have i₁ := eq106538
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq106538
    | exact resolve eq106538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106538
  have eq107109 : ∀ X0 : G, y ≠ (M.op y y) ∨ (k (M.op y y) (M.op X0 y)) = (M.op (M.op y y) (M.op y y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq68 y y x
       have i₂ := eq106903
       grind)
    | exact superpose eq106903 eq68
    | exact resolve eq68 eq106903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107130 : ∀ X0 : G, (k (M.op y y) (M.op X0 y)) = (M.op (M.op y y) (M.op y y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq107109 X0
       grind)
    | (have r₁ := eq107109 X0
       have r₂ := eq106903
       grind)
    | exact resolve eq107109 eq106903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107109
  have eq107161 : ∀ X0 : G, y = (k (M.op y y) (M.op X0 y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq107130 X0
       have i₂ := eq97142
       grind)
    | exact superpose eq97142 eq107130
    | (have j0 := eq107130 X0
       grind)
    | exact resolve eq107130 eq97142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97142 eq107130
  have eq107178 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq107161 X0
       have i₂ := eq106903
       grind)
    | exact superpose eq106903 eq107161
    | (have j0 := eq107161 X0
       grind)
    | exact resolve eq107161 eq106903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106903 eq107161
  have eq253251 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op X0 y)) (σ y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq16102 (M.op X0 y) y
       have i₂ := eq107178 X0
       grind)
    | exact superpose eq107178 eq16102
    | (have j0 := eq16102 (M.op X0 y) y
       have j1 := eq107178 X0
       grind)
    | exact resolve eq16102 eq107178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16102 eq107178
  have eq253324 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq253251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253251
  have eq837810 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq253324 (M.op x x)
       have i₂ := eq17708 x
       grind)
    | exact superpose eq17708 eq253324
    | exact resolve eq253324 eq17708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17708 eq253324
  have eq837976 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq837810
  have eq838079 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq837976
       grind)
    | exact superpose eq837976 eq16
    | exact resolve eq16 eq837976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838144 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq837976
       grind)
    | exact superpose eq837976 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq837976
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq837976
       grind)
    | exact resolve eq13 eq837976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837976
  have eq838169 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq838144
  have eq838184 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq838169
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq838169
    | exact resolve eq838169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838169
  have eq838222 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq838184
       have i₂ := eq3891 y
       grind)
    | exact superpose eq3891 eq838184
    | exact resolve eq838184 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838184
  have eq838244 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq838222
       have i₂ := eq105762
       grind)
    | exact superpose eq105762 eq838222
    | exact resolve eq838222 eq105762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105762 eq838222
  have eq838251 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq838244
       have i₂ := eq3891 x
       grind)
    | exact superpose eq3891 eq838244
    | exact resolve eq838244 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838244
  have eq851394 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3858 x
       have i₂ := eq838251
       grind)
    | exact superpose eq838251 eq3858
    | (have j0 := eq3858 x
       grind)
    | (have r₁ := eq3858 x
       have r₂ := eq838251
       grind)
    | exact resolve eq3858 eq838251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838251
  have eq851485 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq851394
  have eq851527 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq3858 x
       grind)
    | (have r₁ := eq851485
       have r₂ := eq3858 x
       grind)
    | exact resolve eq851485 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851485
  have eq851549 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq851527
       have i₂ := eq3891 x
       grind)
    | exact superpose eq3891 eq851527
    | exact resolve eq851527 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851527
  have eq851605 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq851549
       grind)
    | exact superpose eq851549 eq10
    | exact resolve eq10 eq851549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851549
  have eq852210 : y = (k y x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq851605
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq851605
    | exact resolve eq851605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851605
  have eq853052 : y ≠ y ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16333 y x
       have i₂ := eq852210
       grind)
    | exact superpose eq852210 eq16333
    | (have j0 := eq16333 y x
       grind)
    | (have r₁ := eq16333 y x
       have r₂ := eq852210
       grind)
    | exact resolve eq16333 eq852210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16333 eq852210
  have eq853147 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq853052
  have eq853237 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq838079
       have i₂ := eq853147
       grind)
    | exact superpose eq853147 eq838079
    | exact resolve eq838079 eq853147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838079 eq853147
  have eq853278 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq853237
  have eq853854 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3858 x
       have i₂ := eq853278
       grind)
    | exact superpose eq853278 eq3858
    | (have j0 := eq3858 x
       grind)
    | (have r₁ := eq3858 x
       have r₂ := eq853278
       grind)
    | exact resolve eq3858 eq853278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853278
  have eq853945 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq853854
  have eq853987 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq3858 x
       grind)
    | (have r₁ := eq853945
       have r₂ := eq3858 x
       grind)
    | exact resolve eq853945 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858 eq853945
  have eq854007 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq853987
       have i₂ := eq3891 x
       grind)
    | exact superpose eq3891 eq853987
    | exact resolve eq853987 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891 eq853987
  have eq854047 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq854007
       grind)
    | exact superpose eq854007 eq10
    | exact resolve eq10 eq854007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854622 : x = (M.op x x) := by
    first
    | (have i₁ := eq854047
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq854047
    | exact resolve eq854047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854047
  have eq855380 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq854622
       grind)
    | exact superpose eq854622 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq854622
       grind)
    | exact resolve eq12 eq854622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854622
  have eq855488 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq855380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855380
  have eq856069 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16039
       have i₂ := eq855488 y
       grind)
    | exact superpose eq855488 eq16039
    | exact resolve eq16039 eq855488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16039 eq855488
  have eq856076 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq856069
  have eq857158 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq856076
       grind)
    | exact superpose eq856076 eq16
    | exact resolve eq16 eq856076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857174 : (σ x) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4189 x (σ y)
       have i₂ := eq856076
       grind)
    | exact superpose eq856076 eq4189
    | exact resolve eq4189 eq856076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189
  have eq857300 : (σ x) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq857174
       have i₂ := eq856076
       grind)
    | exact superpose eq856076 eq857174
    | exact resolve eq857174 eq856076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857174
  have eq857332 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq857300
       have i₂ := eq854007
       grind)
    | exact superpose eq854007 eq857300
    | exact resolve eq857300 eq854007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857300
  have eq858030 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq856076
       have i₂ := eq857332
       grind)
    | exact superpose eq857332 eq856076
    | exact resolve eq856076 eq857332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856076 eq857332
  have eq859138 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq858030
       grind)
    | exact superpose eq858030 eq10
    | exact resolve eq10 eq858030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858030
  have eq859740 : x = y := by
    first
    | (have i₁ := eq859138
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq859138
    | exact resolve eq859138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859138
  have eq860795 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq857158
       have i₂ := eq859740
       grind)
    | exact superpose eq859740 eq857158
    | exact resolve eq857158 eq859740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857158 eq859740
  have eq860801 : False := by grind
  exact eq860801

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq31 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq31 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq36 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq37 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq37 X0 X1
       grind)
    | (have r₁ := eq42 X0 (M.op X1 X1)
       have r₂ := eq37 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq37 (k X1 X1) X1
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq42
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | exact resolve eq45 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq45
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq106 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq48 X0 X0
       grind)
    | exact resolve eq102 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq102
  have eq214 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq106 (σ X1) (σ X0)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq106 X1 X0
       grind)
    | exact superpose eq106 eq214
    | exact resolve eq214 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq214
  have eq223 : False := by grind
  exact eq223

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq23
    | exact resolve eq23 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq57 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq60 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq10
    | exact resolve eq10 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq15
    | (have j1 := eq69 X0 X1
       grind)
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) ∨ (σ (M.op X1 X0)) = (k (σ X0) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq71
    | (have j0 := eq71 (M.op X0 (M.op X1 X0)) X0
       grind)
    | exact resolve eq71 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 y x
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 y x
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq83 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq69 (σ y) (σ x)
       grind)
    | exact superpose eq69 eq74
    | (have j1 := eq69 y x
       grind)
    | (have r₁ := eq74
       have r₂ := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq84 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq83
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq58 y
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq58
    | exact resolve eq58 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq58 x
       grind)
    | exact superpose eq58 eq88
    | exact resolve eq88 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq93 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq92
  have eq97 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq59 (σ y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq59
    | exact resolve eq59 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq93
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq93
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq103 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq60 x
       grind)
    | exact superpose eq60 eq103
    | exact resolve eq103 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq104
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq104
       grind)
    | exact resolve eq13 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, y ≠ (M.op x x) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq203 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 (M.op X1 X0))) (σ (M.op X0 (M.op X1 X0)))) ∨ (σ (M.op X1 X0)) = (k (σ X0) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X0 (M.op X1 X0))
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq58
    | (have j1 := eq73 X0 X1
       grind)
    | exact resolve eq58 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 (M.op X1 X0))) (σ (M.op X0 (M.op X1 X0)))) ∨ (σ (M.op X1 X0)) = (k (σ X0) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq255 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq110 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq261 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq15
    | exact resolve eq15 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq269 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq261
       grind)
    | exact superpose eq261 eq16
    | exact resolve eq16 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq632 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq100 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq636 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq269
       have i₂ := eq632
       grind)
    | exact superpose eq632 eq269
    | (have r₁ := eq269
       have r₂ := eq632
       grind)
    | exact resolve eq269 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq632
  have eq640 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq636
  have eq654 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq640
       grind)
    | exact superpose eq640 eq58
    | exact resolve eq58 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq658 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq654
  have eq662 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq101 X0
       grind)
    | (have r₁ := eq101 X0
       have r₂ := eq658
       grind)
    | exact resolve eq101 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq677 : y = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq10
    | exact resolve eq10 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : y = (M.op x x) := by
    first
    | (have i₁ := eq677
       have i₂ := eq60 x
       grind)
    | exact superpose eq60 eq677
    | exact resolve eq677 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq688 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (k X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq662 X0
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq662
    | exact resolve eq662 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq693 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq111 X0
       grind)
    | (have r₁ := eq111 X0
       have r₂ := eq680
       grind)
    | exact resolve eq111 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq697 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq9
    | exact resolve eq9 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq45 x x
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq45
    | exact resolve eq45 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq702 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = y ∨ (M.op X0 X0) ≠ y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq693 X0
       grind)
    | exact superpose eq693 eq15
    | exact resolve eq15 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq726 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq723
    | exact resolve eq723 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq789 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq726 (M.op x y)
       have i₂ := eq697
       grind)
    | exact superpose eq697 eq726
    | exact resolve eq726 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq726
  have eq985 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq688 (σ (M.op x y))
       have i₂ := eq789
       grind)
    | exact superpose eq789 eq688
    | exact resolve eq688 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq789
  have eq1034 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq9 (σ (M.op x y)) (M.op (σ x) (σ x))
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq9
    | exact resolve eq9 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1121 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ x = y ∨ (k (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq702 X0
       grind)
    | exact superpose eq702 eq15
    | (have j1 := eq702 X0
       grind)
    | exact resolve eq15 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq1186 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq207 x x
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq207
    | exact resolve eq207 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1235 : (M.op (σ x) (σ x)) = (k (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1186
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq1186
    | exact resolve eq1186 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq5613 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq69 (σ x) (σ (M.op x y))
       have i₂ := eq1235
       grind)
    | exact superpose eq1235 eq69
    | (have j0 := eq69 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq69 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1235
  have eq5616 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5613
  have eq5644 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq5616
       grind)
    | exact superpose eq5616 eq1034
    | exact resolve eq1034 eq5616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5616
  have eq6019 : (σ (M.op (σ x) (σ x))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq58 (σ (M.op x y))
       have i₂ := eq5644
       grind)
    | exact superpose eq5644 eq58
    | exact resolve eq58 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq6041 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ (σ x)) (σ (σ x))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq6019
       have i₂ := eq58 (σ x)
       grind)
    | exact superpose eq58 eq6019
    | exact resolve eq6019 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6019
  have eq31448 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ (σ x)) (σ (σ x))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6041
       grind)
    | exact superpose eq6041 eq16
    | exact resolve eq16 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041
  have eq31536 : (M.op (σ x) (M.op (σ x) (σ x))) ≠ (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ (σ x)) (σ (σ x))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq31448
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq31448
    | exact resolve eq31448 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31448
  have eq31537 : (M.op (σ (σ x)) (σ (σ x))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by grind
  clear eq31536
  have eq31608 : (τ (M.op (σ (σ x)) (σ (σ x)))) = (M.op (τ (σ (σ (M.op x y)))) (τ (σ (σ (M.op x y))))) := by
    first
    | (have i₁ := eq59 (σ (σ (M.op x y)))
       have i₂ := eq31537
       grind)
    | exact superpose eq31537 eq59
    | exact resolve eq59 eq31537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31537
  have eq31679 : (τ (M.op (σ (σ x)) (σ (σ x)))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq31608
       have i₂ := eq10 (σ (M.op x y))
       grind)
    | exact superpose eq10 eq31608
    | exact resolve eq31608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31608
  have eq31724 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq31679
       have i₂ := eq60 (σ x)
       grind)
    | exact superpose eq60 eq31679
    | exact resolve eq31679 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31679
  have eq31799 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ (M.op x y)) X0) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op x y)) X0
       have i₂ := eq31724
       grind)
    | exact superpose eq31724 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq31724
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq31724
       grind)
    | exact resolve eq13 eq31724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31801 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq59 (σ (M.op x y))
       have i₂ := eq31724
       grind)
    | exact superpose eq31724 eq59
    | exact resolve eq59 eq31724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31724
  have eq31866 : (τ (M.op (σ x) (σ x))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq31801
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq31801
    | exact resolve eq31801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31801
  have eq31913 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq31866
       have i₂ := eq60 x
       grind)
    | exact superpose eq60 eq31866
    | exact resolve eq31866 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq31866
  have eq31930 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq31913
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq31913
    | exact resolve eq31913 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31913
  have eq31980 : y ≠ y ∨ x = y ∨ (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1121 (M.op x y)
       have i₂ := eq31930
       grind)
    | exact superpose eq31930 eq1121
    | (have j0 := eq1121 (M.op x y)
       grind)
    | (have r₁ := eq1121 (M.op x y)
       have r₂ := eq31930
       grind)
    | exact resolve eq1121 eq31930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq31930
  have eq32013 : x = y ∨ (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq31980
  have eq32040 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq32013
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq32013
    | exact resolve eq32013 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq32013
  have eq32078 : (M.op (σ x) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq32040
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq32040
    | exact resolve eq32040 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32040
  have eq36939 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq31799 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31799
  have eq36958 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq36939
       have i₂ := eq32078
       grind)
    | exact superpose eq32078 eq36939
    | exact resolve eq36939 eq32078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32078 eq36939
  have eq37016 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1034
       have i₂ := eq36958
       grind)
    | exact superpose eq36958 eq1034
    | exact resolve eq1034 eq36958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034 eq36958
  have eq37037 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq37016
       grind)
    | exact superpose eq37016 eq16
    | exact resolve eq16 eq37016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37016
  have eq37139 : (M.op (σ x) (M.op (σ x) (σ x))) ≠ (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37037
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq37037
    | exact resolve eq37037 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq37037
  have eq37140 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq37139
  have eq37241 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq59 (σ x)
       have i₂ := eq37140
       grind)
    | exact superpose eq37140 eq59
    | exact resolve eq59 eq37140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq37140
  have eq37279 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq37241
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37241
    | exact resolve eq37241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37241
  have eq37330 : x = y ∨ x = y := by
    first
    | (have i₁ := eq37279
       have i₂ := eq680
       grind)
    | exact superpose eq680 eq37279
    | exact resolve eq37279 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq37279
  have eq37331 : x = y := by grind
  clear eq37330
  have eq37425 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37331
       grind)
    | exact superpose eq37331 eq16
    | exact resolve eq16 eq37331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37331
  have eq37808 : False := by grind
  exact eq37808

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1481 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  clear eq19
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq509 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq512 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq3140 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq512
    | exact resolve eq512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq3190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3140 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3140
    | (have j0 := eq3140 X0 X1
       grind)
    | exact resolve eq3140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq3439 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq509 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq509 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq509 (σ X1) X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq509 X0 X1
       grind)
    | exact resolve eq13 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3442 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq509 (σ x) y
       grind)
    | exact superpose eq509 eq16
    | (have j1 := eq509 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq509 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq3451 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3452 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3451 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3459 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3442
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3442
    | exact resolve eq3442 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3472 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3459
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3459
    | exact resolve eq3459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3693 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3452 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3452
    | exact resolve eq3452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452
  have eq3789 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3693 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3693
    | (have j0 := eq3693 X0 X1
       grind)
    | exact resolve eq3693 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3693
  have eq3817 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3789 X1 X0
       grind)
    | exact superpose eq3789 eq11
    | (have j1 := eq3789 X1 X0
       grind)
    | exact resolve eq11 eq3789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq3936 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3817 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3817
    | (have j0 := eq3817 X0 X1
       grind)
    | exact resolve eq3817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq4018 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3936 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3936
    | (have j0 := eq3936 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4067 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3936 X0 (τ X1)
       grind)
    | exact superpose eq3936 eq18
    | (have j1 := eq3936 X0 (τ X1)
       grind)
    | exact resolve eq18 eq3936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3936
  have eq4176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4018 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4018
    | (have j0 := eq4018 X0 X1
       grind)
    | exact resolve eq4018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4289 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4067 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4067
    | exact resolve eq4067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4067
  have eq4346 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4289 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4289
    | (have j0 := eq4289 X0 X1
       grind)
    | exact resolve eq4289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq12079 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4176 y x
       grind)
    | exact superpose eq4176 eq16
    | (have j1 := eq4176 y x
       grind)
    | exact resolve eq16 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176
  have eq12189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12079
       have i₂ := eq3190 y x
       grind)
    | exact superpose eq3190 eq12079
    | (have j1 := eq3190 y x
       grind)
    | (have r₁ := eq12079
       have r₂ := eq3190 y x
       grind)
    | (have r₁ := eq12079
       have r₂ := eq3190 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12079
       have r₂ := eq3190 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12079 eq3190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq12190 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12189
  have eq12320 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12190
       grind)
    | exact superpose eq12190 eq16
    | exact resolve eq16 eq12190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq12321 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12320
       have r₂ := eq22 x
       grind)
    | exact resolve eq12320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12320
  have eq12322 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3472
       have i₂ := eq12321
       grind)
    | exact superpose eq12321 eq3472
    | (have r₁ := eq3472
       have r₂ := eq12321
       grind)
    | exact resolve eq3472 eq12321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12321
  have eq12328 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12322
  have eq12329 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12328
  have eq12330 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12329
       have r₂ := eq3472
       grind)
    | exact resolve eq12329 eq3472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472 eq12329
  have eq12332 : y = (τ (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12330
       grind)
    | exact superpose eq12330 eq10
    | exact resolve eq10 eq12330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12330
  have eq12397 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12332
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12332
    | exact resolve eq12332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12332
  have eq12399 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12397
       grind)
    | exact superpose eq12397 eq16
    | exact resolve eq16 eq12397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12397
  have eq12400 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12399
       have r₂ := eq22 x
       grind)
    | exact resolve eq12399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12399
  have eq12415 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq12400
       grind)
    | exact superpose eq12400 eq11
    | exact resolve eq11 eq12400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12400
  have eq12512 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12415
       grind)
    | exact superpose eq12415 eq16
    | exact resolve eq16 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12415
  have eq12554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12512
       have i₂ := eq4346 y x
       grind)
    | exact superpose eq4346 eq12512
    | (have j1 := eq4346 y x
       grind)
    | (have r₁ := eq12512
       have r₂ := eq4346 y x
       grind)
    | (have r₁ := eq12512
       have r₂ := eq4346 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12512
       have r₂ := eq4346 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12512 eq4346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4346
  have eq12555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12512
       have i₂ := eq3190 y x
       grind)
    | exact superpose eq3190 eq12512
    | (have j1 := eq3190 y x
       grind)
    | (have r₁ := eq12512
       have r₂ := eq3190 y x
       grind)
    | (have r₁ := eq12512
       have r₂ := eq3190 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12512
       have r₂ := eq3190 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12512 eq3190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3190
  have eq12556 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq12555
  have eq12557 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq12554
  have eq12563 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12512
       have i₂ := eq12556
       grind)
    | exact superpose eq12556 eq12512
    | exact resolve eq12512 eq12556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12556
  have eq12564 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq12563
  have eq12565 : (M.op x y) = (M.op x x) := by grind
  clear eq12564
  have eq12882 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12512
       have i₂ := eq12557
       grind)
    | exact superpose eq12557 eq12512
    | exact resolve eq12512 eq12557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12883 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq12882
  have eq12884 : (k y x) = (M.op x x) := by grind
  clear eq12883
  have eq12894 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12512
       have i₂ := eq12884
       grind)
    | exact superpose eq12884 eq12512
    | exact resolve eq12512 eq12884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12512 eq12884
  have eq12924 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12894
       have i₂ := eq12565
       grind)
    | exact superpose eq12565 eq12894
    | exact resolve eq12894 eq12565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12565 eq12894
  have eq12925 : False := by grind
  exact eq12925

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y (M.op x X0))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq44
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq44 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq130 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130
    | exact resolve eq130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq151
    | exact resolve eq151 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq156 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq154
       have i₂ := eq69 sF0
       grind)
    | exact superpose eq69 eq154
    | exact resolve eq154 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq177 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq156 eq16
    | exact resolve eq16 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq199
       have r₂ := eq27
       grind)
    | exact resolve eq199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq204 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq202
    | exact resolve eq202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq206 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204 eq27
    | exact resolve eq27 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq88 (σ X0) sF3
       grind)
    | exact superpose eq88 eq40
    | (have j1 := eq88 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq88
  have eq258 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq271 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq204 eq51
    | exact resolve eq51 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq279 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq271 eq14
    | exact resolve eq14 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq271 eq14
    | exact resolve eq14 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq310 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq282
    | (have j0 := eq282 (σ x)
       grind)
    | exact resolve eq282 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq328 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204 eq310
    | exact resolve eq310 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq333 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq328
  have eq485 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X0 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq55 X0 (M.op x X2) (M.op X0 X2)
       have i₂ := eq55 X2 x X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq665 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204 eq81
    | (have r₁ := eq81
       have r₂ := eq204
       grind)
    | exact resolve eq81 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq204
  have eq666 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq665
  have eq1893 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq666 eq279
    | exact resolve eq279 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq666
  have eq1934 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1893
  have eq1992 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1934 eq333
    | exact resolve eq333 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq1934
  have eq2022 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1992
  have eq2067 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2022 eq131
    | exact resolve eq131 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq2071 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2067
  have eq2076 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2071
       have r₂ := eq206
       grind)
    | exact resolve eq2071 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq2071
  have eq2079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2076 eq26
    | exact resolve eq26 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2087 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2076 eq131
    | exact resolve eq131 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq2076
  have eq2180 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2087
  have eq2185 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2180
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq2180
    | exact resolve eq2180 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2185 eq2079
    | exact resolve eq2079 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079 eq2185
  have eq2352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2333
  have eq2362 : y = (M.op x y) := by
    first
    | (have r₁ := eq2352
       have r₂ := eq27
       grind)
    | exact resolve eq2352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2365 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2362 eq20
    | exact resolve eq20 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2369 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq2362 eq80
    | (have r₁ := eq80
       have r₂ := eq2362
       grind)
    | exact resolve eq80 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2375 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq2362 eq258
    | exact resolve eq258 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq2378 : (M.op y x) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq2369
  have eq2384 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2365
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2365
    | exact resolve eq2365 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2388 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2384 eq26
    | exact resolve eq26 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2558 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq485 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq485
    | (have j0 := eq485 x y
       grind)
    | exact resolve eq485 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq2632 : y = (M.op x (M.op y x)) := by
    first
    | exact superpose eq2362 eq2558
    | exact resolve eq2558 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2637 : x = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq14 x y x
       have i₂ := eq2632
       grind)
    | exact superpose eq2632 eq14
    | exact resolve eq14 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq3788 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq2384 eq221
    | (have j0 := eq221 X0
       grind)
    | exact resolve eq221 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq3789 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2384 eq3788
    | (have j0 := eq3788 X0
       grind)
    | exact resolve eq3788 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq3826 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3789 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3789
    | (have j0 := eq3789 x
       grind)
    | exact resolve eq3789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq3847 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2388 eq3826
    | exact resolve eq3826 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826
  have eq3863 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3847
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3847
    | exact resolve eq3847 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3847
  have eq3873 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2384 eq3863
    | exact resolve eq3863 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2388 eq3873
    | exact resolve eq3873 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388 eq3873
  have eq3881 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3878
       have r₂ := eq27
       grind)
    | exact resolve eq3878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq3887 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3881 eq64
    | exact resolve eq64 eq3881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3889 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2362 eq3887
    | exact resolve eq3887 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq5188 : (M.op y x) = (M.op y y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2378
       have i₂ := eq3889
       grind)
    | exact superpose eq3889 eq2378
    | exact resolve eq2378 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378 eq3889
  have eq5192 : y = (M.op (M.op y x) y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2375
       have i₂ := eq5188
       grind)
    | exact superpose eq5188 eq2375
    | exact resolve eq2375 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq5188
  have eq5226 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq5192
       have i₂ := eq2637
       grind)
    | exact superpose eq2637 eq5192
    | exact resolve eq5192 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637 eq5192
  have eq5232 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5226 eq15
    | exact resolve eq15 eq5226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5226
  have eq5245 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5232
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5232
    | exact resolve eq5232 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5232
  have eq5247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2384 eq5245
    | exact resolve eq5245 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245
  have eq5248 : x = y := by
    first
    | (have r₁ := eq5247
       have r₂ := eq27
       grind)
    | exact resolve eq5247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247
  have eq5249 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5248
       grind)
    | exact superpose eq5248 eq18
    | exact resolve eq18 eq5248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5250 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5248
       grind)
    | exact superpose eq5248 eq24
    | exact resolve eq24 eq5248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5254 : (σ (k x (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq96
       have i₂ := eq5248
       grind)
    | exact superpose eq5248 eq96
    | exact resolve eq96 eq5248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq5301 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2384 eq5254
    | exact resolve eq5254 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5254
  have eq5305 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2384 eq5250
    | exact resolve eq5250 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384 eq5250
  have eq5306 : y = (M.op x x) := by
    first
    | exact superpose eq2362 eq5249
    | exact resolve eq5249 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5249
  have eq5314 : (σ (k x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5301
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq5301
    | exact resolve eq5301 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq5301
  have eq5318 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5305
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5305
    | exact resolve eq5305 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5305
  have eq5319 : x = (M.op x x) := by
    first
    | (have i₁ := eq5306
       have i₂ := eq5248
       grind)
    | exact superpose eq5248 eq5306
    | exact resolve eq5306 eq5248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5324 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq5314
    | exact resolve eq5314 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5314
  have eq5330 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3881 eq5324
    | exact resolve eq5324 eq3881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3881 eq5324
  have eq5617 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5330 eq177
    | exact resolve eq177 eq5330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq5330
  have eq5635 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2362 eq5617
    | exact resolve eq5617 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362 eq5617
  have eq5638 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5635
       have i₂ := eq5248
       grind)
    | exact superpose eq5248 eq5635
    | exact resolve eq5635 eq5248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248 eq5635
  have eq5639 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5638
       have i₂ := eq5319
       grind)
    | exact superpose eq5319 eq5638
    | exact resolve eq5638 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319 eq5638
  have eq5643 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5639 eq15
    | exact resolve eq15 eq5639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639
  have eq5666 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5643
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5643
    | exact resolve eq5643 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5643
  have eq5668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5318 eq5666
    | exact resolve eq5666 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5318 eq5666
  have eq5670 : False := by grind
  exact eq5670

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq271 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq272 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 X0 X1
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq782 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq278 x y
       grind)
    | exact superpose eq278 eq16
    | (have j1 := eq278 x y
       grind)
    | exact resolve eq16 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq815 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq782
  have eq817 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq815
    | exact resolve eq815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq876 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq817 (τ X0) X1
       grind)
    | exact superpose eq817 eq18
    | (have j1 := eq817 (τ X0) X1
       grind)
    | exact resolve eq18 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq817
  have eq1243 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq876 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq876
    | exact resolve eq876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq1291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1243 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1243
    | (have j0 := eq1243 X0 X1
       grind)
    | exact resolve eq1243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1393 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq790
       have i₂ := eq1291 x y
       grind)
    | exact superpose eq1291 eq790
    | (have j1 := eq1291 (σ x) (σ y)
       grind)
    | (have r₁ := eq790
       have r₂ := eq1291 x y
       grind)
    | exact resolve eq790 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1394 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1393
  have eq1419 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1394
  have eq1608 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq790
       have i₂ := eq1419
       grind)
    | exact superpose eq1419 eq790
    | exact resolve eq790 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq1419
  have eq1609 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1608
  have eq1610 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1609
  have eq1616 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1610
  have eq1644 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1616
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1616
    | exact resolve eq1616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1741 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1644
       grind)
    | exact superpose eq1644 eq16
    | exact resolve eq16 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1741
       have i₂ := eq1291 x y
       grind)
    | exact superpose eq1291 eq1741
    | (have j1 := eq1291 x y
       grind)
    | (have r₁ := eq1741
       have r₂ := eq1291 x y
       grind)
    | exact resolve eq1741 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1769 : x = (M.op y y) := by grind
  clear eq1768
  have eq1803 : (M.op x y) = (k x y) := by grind
  clear eq1769
  have eq1830 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1741
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq1741
    | exact resolve eq1741 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741 eq1803
  have eq1833 : False := by grind
  exact eq1833

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq273 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq274 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq278 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq777 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq279 x y
       grind)
    | exact superpose eq279 eq16
    | (have j1 := eq279 x y
       grind)
    | exact resolve eq16 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq817 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq777
    | (have j0 := eq777 X0 X1
       grind)
    | exact resolve eq777 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq777
  have eq818 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq817
    | exact resolve eq817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq877 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq818 (τ X1) X0
       grind)
    | exact superpose eq818 eq18
    | (have j1 := eq818 (τ X1) X0
       grind)
    | exact resolve eq18 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq818
  have eq1244 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq877 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq877
    | exact resolve eq877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq1292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1244
    | (have j0 := eq1244 X0 X1
       grind)
    | exact resolve eq1244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1394 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq791
       have i₂ := eq1292 y x
       grind)
    | exact superpose eq1292 eq791
    | (have j1 := eq1292 (σ y) (σ x)
       grind)
    | (have r₁ := eq791
       have r₂ := eq1292 y x
       grind)
    | exact resolve eq791 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1395 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1394
  have eq1398 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1395
  have eq1480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq791
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq791
    | exact resolve eq791 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq1398
  have eq1481 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1480
  have eq1482 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1481
  have eq1488 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1482
  have eq1515 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1488
    | exact resolve eq1488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1592 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1515
       grind)
    | exact superpose eq1515 eq16
    | exact resolve eq16 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1618 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1592
       have i₂ := eq1292 y x
       grind)
    | exact superpose eq1292 eq1592
    | (have j1 := eq1292 y x
       grind)
    | (have r₁ := eq1592
       have r₂ := eq1292 y x
       grind)
    | exact resolve eq1592 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1619 : y = (M.op x x) := by grind
  clear eq1618
  have eq1711 : (M.op x y) = (k y x) := by grind
  clear eq1619
  have eq1738 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1592
       have i₂ := eq1711
       grind)
    | exact superpose eq1711 eq1592
    | exact resolve eq1592 eq1711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592 eq1711
  have eq1741 : False := by grind
  exact eq1741

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq273 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq273
    | (have j0 := eq273 X0 X1
       grind)
    | exact resolve eq273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq271 X0 X1
       grind)
    | (have r₁ := eq275 X0 X1
       have r₂ := eq271 X0 X1
       grind)
    | (have r₁ := eq275 X0 (k X1 X0)
       have r₂ := eq271 X0 X1
       grind)
    | (have r₁ := eq275 X0 X0
       have r₂ := eq271 X0 X0
       grind)
    | exact resolve eq275 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq275
  have eq780 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq279 x y
       grind)
    | exact superpose eq279 eq16
    | (have j1 := eq279 x y
       grind)
    | exact resolve eq16 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq820 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq780
    | (have j0 := eq780 X0 X1
       grind)
    | exact resolve eq780 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq780
  have eq825 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq820
    | exact resolve eq820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq958 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq825 (τ X1) X0
       grind)
    | exact superpose eq825 eq18
    | (have j1 := eq825 (τ X1) X0
       grind)
    | exact resolve eq18 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq825
  have eq1248 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq958 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq958
    | exact resolve eq958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1296 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1248 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1248
    | (have j0 := eq1248 X0 X1
       grind)
    | exact resolve eq1248 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq794
       have i₂ := eq1296 y x
       grind)
    | exact superpose eq1296 eq794
    | (have j1 := eq1296 (σ y) (σ x)
       grind)
    | (have r₁ := eq794
       have r₂ := eq1296 y x
       grind)
    | exact resolve eq794 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1398
  have eq1426 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1399
  have eq1450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq794
       have i₂ := eq1426
       grind)
    | exact superpose eq1426 eq794
    | exact resolve eq794 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq1426
  have eq1451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1450
  have eq1452 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1451
  have eq1521 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1452
  have eq1546 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1521
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1521
    | exact resolve eq1521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1552 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1546
       grind)
    | exact superpose eq1546 eq16
    | exact resolve eq16 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq1296 y x
       grind)
    | exact superpose eq1296 eq1552
    | (have j1 := eq1296 y x
       grind)
    | (have r₁ := eq1552
       have r₂ := eq1296 y x
       grind)
    | exact resolve eq1552 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296
  have eq1652 : y = (M.op x x) := by grind
  clear eq1651
  have eq1657 : (M.op x y) = (k y x) := by grind
  clear eq1652
  have eq1775 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq1657
       grind)
    | exact superpose eq1657 eq1552
    | exact resolve eq1552 eq1657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq1657
  have eq1778 : False := by grind
  exact eq1778
