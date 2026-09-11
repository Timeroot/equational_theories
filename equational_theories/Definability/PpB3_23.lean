import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_x_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
    | (have i₁ := eq64 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq64
    | exact resolve eq64 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
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
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq275 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) = (k (τ (τ (M.op (σ (σ X0)) (σ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (τ (M.op (σ (σ X0)) (σ (σ X0)))) X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq23
    | exact resolve eq23 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq728 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq728 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq728
    | (have j0 := eq728 X0 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq728 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq951 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq728 X1 X0
       grind)
    | exact superpose eq728 eq15
    | (have j1 := eq728 X0 X0
       grind)
    | exact resolve eq15 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3338 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x
       have i₂ := eq751 (τ x) x
       grind)
    | exact superpose eq751 eq25
    | (have j1 := eq751 (τ X0) X0
       grind)
    | exact resolve eq25 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq751
  have eq3345 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq3338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3347 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3345 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3345
    | (have j0 := eq3345 X0
       grind)
    | exact resolve eq3345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3403 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq3347 (τ X0)
       grind)
    | exact superpose eq3347 eq19
    | (have j1 := eq3347 (τ X0)
       grind)
    | exact resolve eq19 eq3347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347
  have eq3409 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3403 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq3403
    | (have j0 := eq3403 X0
       grind)
    | exact resolve eq3403 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3403
  have eq3425 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3409 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3409
    | (have j0 := eq3409 X0
       grind)
    | exact resolve eq3409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq6266 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ (τ X0)) X1
       have i₂ := eq3425 X0
       grind)
    | exact superpose eq3425 eq76
    | (have j1 := eq3425 X0
       grind)
    | exact resolve eq76 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6314 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq523 (τ (τ X0)) (τ (τ X0)) x
       have i₂ := eq3425 X0
       grind)
    | exact superpose eq3425 eq523
    | (have j1 := eq3425 X0
       grind)
    | exact resolve eq523 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425
  have eq6334 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6314 X0 X1
       have i₂ := eq89 (τ (τ X0)) X1
       grind)
    | exact superpose eq89 eq6314
    | (have j0 := eq6314 X0 X1
       grind)
    | exact resolve eq6314 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314
  have eq12061 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq6334 eq6266
    | (have j0 := eq6266 X0 X1
       have j1 := eq6334 X0 X1
       grind)
    | exact resolve eq6266 eq6334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6266
  have eq12217 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | exact superpose eq12061 eq6334
    | (have j0 := eq6334 X0 X1
       have j1 := eq12061 X0 X1
       grind)
    | exact resolve eq6334 eq12061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6334 eq12061
  have eq13553 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq12217 (σ X0) X1
       grind)
    | exact superpose eq12217 eq23
    | (have j1 := eq12217 (σ X0) X1
       grind)
    | exact resolve eq23 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12217
  have eq13601 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13553 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13553
    | (have j0 := eq13553 X0 X1
       grind)
    | exact resolve eq13553 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13553
  have eq13642 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13601 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13601
    | (have j0 := eq13601 X0 X1
       grind)
    | exact resolve eq13601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13601
  have eq13678 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13642 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13642
    | (have j0 := eq13642 X0 X1
       grind)
    | exact resolve eq13642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13642
  have eq13752 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13678 (σ X0) X1
       grind)
    | exact superpose eq13678 eq23
    | (have j1 := eq13678 (σ X0) X1
       grind)
    | exact resolve eq23 eq13678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13678
  have eq13800 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13752 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13752
    | (have j0 := eq13752 X0 X1
       grind)
    | exact resolve eq13752 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13752
  have eq13841 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13800 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13800
    | (have j0 := eq13800 X0 X1
       grind)
    | exact resolve eq13800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13800
  have eq13877 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13841 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13841
    | (have j0 := eq13841 X0 X1
       grind)
    | exact resolve eq13841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13841
  have eq13951 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13877 (σ X0) X1
       grind)
    | exact superpose eq13877 eq23
    | (have j1 := eq13877 (σ X0) X1
       grind)
    | exact resolve eq23 eq13877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13877
  have eq13999 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13951 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13951
    | (have j0 := eq13951 X0 X1
       grind)
    | exact resolve eq13951 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13951
  have eq14039 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13999 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13999
    | (have j0 := eq13999 X0 X1
       grind)
    | exact resolve eq13999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999
  have eq19582 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq951
  have eq19598 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq19582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq19614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq14039 eq19598
    | (have j0 := eq19598 X0
       have j1 := eq14039 X0 (σ X0)
       grind)
    | exact resolve eq19598 eq14039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14039 eq19598
  have eq19641 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19614 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq19614
    | (have j0 := eq19614 X0
       have j1 := eq14 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq19614 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19653 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq19614 (τ X0)
       grind)
    | exact superpose eq19614 eq19
    | (have j1 := eq19614 (τ X0)
       grind)
    | exact resolve eq19 eq19614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19658 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq19614 X0
       grind)
    | exact superpose eq19614 eq10
    | (have j1 := eq19614 X0
       grind)
    | exact resolve eq10 eq19614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19614
  have eq19725 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19641
  have eq19730 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19653 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19653
    | (have j0 := eq19653 X0
       grind)
    | exact resolve eq19653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19653
  have eq19745 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19730 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19730
    | (have j0 := eq19730 X0
       grind)
    | exact resolve eq19730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19730
  have eq19761 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19745 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq19745
    | (have j0 := eq19745 (τ X0)
       grind)
    | exact resolve eq19745 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20286 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq19761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20323 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq20286 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq20286
    | (have j0 := eq20286 (σ X0)
       grind)
    | exact resolve eq20286 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20286
  have eq20341 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq20323 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20323
    | (have j0 := eq20323 X0
       grind)
    | exact resolve eq20323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20323
  have eq20358 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20341 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20341
    | (have j0 := eq20341 X0
       grind)
    | exact resolve eq20341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341
  have eq21502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq925 x y
       grind)
    | exact superpose eq925 eq16
    | (have j1 := eq925 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq925 x y
       grind)
    | exact resolve eq16 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq21655 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq21502
  have eq30337 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq19725 eq926
    | (have j0 := eq926 X0
       have j1 := eq19725 X0
       grind)
    | exact resolve eq926 eq19725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq19725
  have eq30493 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30337
  have eq30540 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq30493 eq19658
    | (have j0 := eq19658 X0
       have j1 := eq30493 X0
       grind)
    | exact resolve eq19658 eq30493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19658 eq30493
  have eq30721 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30540 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq30540
    | (have j0 := eq30540 X0
       grind)
    | exact resolve eq30540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30540
  have eq30894 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq30721 X0
       grind)
    | exact superpose eq30721 eq36
    | (have j1 := eq30721 X0
       grind)
    | exact resolve eq36 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq30895 : ∀ X0 : G, (τ (τ (σ (σ X0)))) = (k (τ (τ (σ (σ X0)))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq420 X0
       have i₂ := eq30721 (σ X0)
       grind)
    | exact superpose eq30721 eq420
    | (have j1 := eq30721 (σ X0)
       grind)
    | exact resolve eq420 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq30721
  have eq31058 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30895 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq30895
    | (have j0 := eq30895 X0
       grind)
    | exact resolve eq30895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30895
  have eq31059 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30894 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30894
    | (have j0 := eq30894 X0
       grind)
    | exact resolve eq30894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30894
  have eq31071 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31058 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31058
    | (have j0 := eq31058 X0
       grind)
    | exact resolve eq31058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31058
  have eq31074 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31071 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq31071
    | (have j0 := eq31071 X0
       grind)
    | exact resolve eq31071 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31071
  have eq31081 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31059 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq31059
    | exact resolve eq31059 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31193 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq31059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31626 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq31059 eq31074
    | (have j0 := eq31074 X0
       have j1 := eq31059 X0
       grind)
    | exact resolve eq31074 eq31059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31074
  have eq31851 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 (σ X0) (σ X0)
       have i₂ := eq31626 X0
       grind)
    | exact superpose eq31626 eq89
    | (have j1 := eq31626 X0
       grind)
    | exact resolve eq89 eq31626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33823 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq31081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31081
  have eq33846 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq31626 X0
       have j1 := eq20358 X0
       grind)
    | (have r₁ := eq31626 X0
       have r₂ := eq20358 X0
       grind)
    | exact resolve eq31626 eq20358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20358 eq31626
  have eq33939 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33846 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33846
    | (have j0 := eq33846 (τ X0)
       grind)
    | exact resolve eq33846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33846
  have eq34125 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq19761 eq33939
    | (have j0 := eq33939 X0
       have j1 := eq19761 X0
       grind)
    | exact resolve eq33939 eq19761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19761 eq33939
  have eq34136 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34125 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq34125
    | (have j0 := eq34125 X0
       grind)
    | exact resolve eq34125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34125
  have eq34167 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k (σ (σ (τ (τ X0)))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq34136 (τ X0)
       grind)
    | exact superpose eq34136 eq275
    | (have j1 := eq34136 (τ X0)
       grind)
    | exact resolve eq275 eq34136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq34136
  have eq34339 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34167 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq34167
    | (have j0 := eq34167 X0
       grind)
    | exact resolve eq34167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34167
  have eq34352 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34339 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34339
    | (have j0 := eq34339 X0
       grind)
    | exact resolve eq34339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34339
  have eq34356 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34352 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq34352
    | (have j0 := eq34352 X0
       grind)
    | exact resolve eq34352 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq34352
  have eq34358 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq31059 eq34356
    | (have j0 := eq34356 X0
       have j1 := eq31059 X0
       grind)
    | exact resolve eq34356 eq31059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31059 eq34356
  have eq34405 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34358 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34358
    | (have j0 := eq34358 (σ X0)
       grind)
    | exact resolve eq34358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34358
  have eq34587 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34405 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq34405
    | (have j0 := eq34405 X0
       grind)
    | exact resolve eq34405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34405
  have eq72885 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34587 x
       have i₂ := eq21655
       grind)
    | exact superpose eq21655 eq34587
    | (have j0 := eq34587 x
       grind)
    | exact resolve eq34587 eq21655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21655 eq34587
  have eq73260 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq33823 x
       grind)
    | (have r₁ := eq72885
       have r₂ := eq33823 x
       grind)
    | exact resolve eq72885 eq33823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33823 eq72885
  have eq73327 : y = (M.op x x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73260
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq73260
    | exact resolve eq73260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73260
  have eq73328 : y = (M.op x x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by grind
  clear eq73327
  have eq73372 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19745 eq73328
    | (have j1 := eq19745 x
       grind)
    | exact resolve eq73328 eq19745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19745 eq73328
  have eq73413 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq73372
  have eq73447 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq73413
       grind)
    | exact superpose eq73413 eq10
    | exact resolve eq10 eq73413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73413
  have eq73667 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73447
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq73447
    | exact resolve eq73447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73447
  have eq73668 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq73667
  have eq73792 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31851 x
       have i₂ := eq73668
       grind)
    | exact superpose eq73668 eq31851
    | (have j0 := eq31851 x
       grind)
    | exact resolve eq31851 eq73668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31851
  have eq73842 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89 x x
       have i₂ := eq73668
       grind)
    | exact superpose eq73668 eq89
    | exact resolve eq89 eq73668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73668
  have eq73917 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have j1 := eq31193 x
       grind)
    | (have r₁ := eq73792
       have r₂ := eq31193 x
       grind)
    | exact resolve eq73792 eq31193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73792
  have eq74579 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73917
       grind)
    | exact superpose eq73917 eq16
    | exact resolve eq16 eq73917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73917
  have eq75082 : (σ y) ≠ (σ y) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74579
       have i₂ := eq73842
       grind)
    | exact superpose eq73842 eq74579
    | exact resolve eq74579 eq73842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73842 eq74579
  have eq75083 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq75082
  have eq75084 : x = (k x x) := by
    first
    | (have j1 := eq31193 x
       grind)
    | (have r₁ := eq75083
       have r₂ := eq31193 x
       grind)
    | exact resolve eq75083 eq31193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31193 eq75083
  have eq75146 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq728 x x
       have i₂ := eq75084
       grind)
    | exact superpose eq75084 eq728
    | (have j0 := eq728 x x
       grind)
    | exact resolve eq728 eq75084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq75147 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq75084
       grind)
    | exact superpose eq75084 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq75084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75084
  have eq75148 : x = (M.op x x) := by grind
  clear eq75147
  have eq75149 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75146
  have eq75179 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq75148
       grind)
    | exact superpose eq75148 eq76
    | exact resolve eq76 eq75148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75293 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq523 x x x
       have i₂ := eq75148
       grind)
    | exact superpose eq75148 eq523
    | exact resolve eq523 eq75148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75148
  have eq75349 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq75293 X0
       have i₂ := eq89 x X0
       grind)
    | exact superpose eq89 eq75293
    | exact resolve eq75293 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq75293
  have eq76911 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 (σ x) X0
       have i₂ := eq75149
       grind)
    | exact superpose eq75149 eq76
    | exact resolve eq76 eq75149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq75149
  have eq78247 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75179 X0
       have i₂ := eq75349 X0
       grind)
    | exact superpose eq75349 eq75179
    | exact resolve eq75179 eq75349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75179 eq75349
  have eq78249 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78247 y
       grind)
    | exact superpose eq78247 eq16
    | exact resolve eq16 eq78247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78371 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 x X1 X0
       have i₂ := eq78247 X0
       grind)
    | exact superpose eq78247 eq523
    | exact resolve eq523 eq78247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq78648 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78371 X0 X0
       have i₂ := eq78247 X0
       grind)
    | exact superpose eq78247 eq78371
    | exact resolve eq78371 eq78247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78247 eq78371
  have eq82130 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76911 X0
       have i₂ := eq78648 X0 (σ x)
       grind)
    | exact superpose eq78648 eq76911
    | exact resolve eq76911 eq78648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76911 eq78648
  have eq82131 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq78249
       have i₂ := eq82130 (σ y)
       grind)
    | exact superpose eq82130 eq78249
    | (have r₁ := eq78249
       have r₂ := eq82130 (σ y)
       grind)
    | exact resolve eq78249 eq82130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78249 eq82130
  have eq82312 : False := by grind
  exact eq82312

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq49 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq83 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq22
    | exact resolve eq22 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq98 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X0) (τ X0)) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq46
    | (have j1 := eq14 (τ (k X1 X0)) (M.op (τ X0) (τ X1))
       grind)
    | exact resolve eq46 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42 y x
       grind)
    | exact superpose eq42 eq16
    | (have j1 := eq42 x y
       grind)
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq276 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq30
  have eq290 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq481 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq290 (σ X0)
       grind)
    | exact superpose eq290 eq49
    | (have j1 := eq290 (σ X0)
       grind)
    | exact resolve eq49 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq290
  have eq507 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq481 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq481
    | (have j0 := eq481 X0
       grind)
    | exact resolve eq481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq514 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq507 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq507
    | (have j0 := eq507 X0
       grind)
    | exact resolve eq507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq1415 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq83
    | exact resolve eq83 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1430 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1415 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1415
    | exact resolve eq1415 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq5888 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (τ (σ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq10
    | (have j1 := eq514 X0
       grind)
    | exact resolve eq10 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq5936 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5888 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq5888
    | (have j0 := eq5888 X0
       grind)
    | exact resolve eq5888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq5985 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq5936 (τ X0)
       grind)
    | exact superpose eq5936 eq19
    | (have j1 := eq5936 (τ X0)
       grind)
    | exact resolve eq19 eq5936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq5994 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5985 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5985
    | (have j0 := eq5985 X0
       grind)
    | exact resolve eq5985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq6017 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5994 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5994
    | (have j0 := eq5994 X0
       grind)
    | exact resolve eq5994 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994
  have eq6037 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6017 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq6017
    | (have j0 := eq6017 X0
       grind)
    | exact resolve eq6017 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq6017
  have eq6052 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6037 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6037
    | (have j0 := eq6037 X0
       grind)
    | exact resolve eq6037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6037
  have eq6079 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6052 (τ X0)
       have i₂ := eq46 X0 X0
       grind)
    | exact superpose eq46 eq6052
    | exact resolve eq6052 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq6052
  have eq30586 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq30596 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq30586 X0
       have j1 := eq6079 X0
       grind)
    | (have r₁ := eq30586 X0
       have r₂ := eq6079 X0
       grind)
    | exact resolve eq30586 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079 eq30586
  have eq30640 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq30596 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30596
    | exact resolve eq30596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30794 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq30640 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq30640
    | exact resolve eq30640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30640
  have eq30812 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30794 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30794
    | exact resolve eq30794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30794
  have eq30906 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq30812 (σ X0)
       grind)
    | exact superpose eq30812 eq15
    | exact resolve eq15 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30963 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30906 X0
       have i₂ := eq30812 X0
       grind)
    | exact superpose eq30812 eq30906
    | exact resolve eq30906 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30906
  have eq33068 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1430 (σ X0) (σ X0)
       have i₂ := eq30963 X0
       grind)
    | exact superpose eq30963 eq1430
    | exact resolve eq1430 eq30963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1474491 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq30596 X0
       grind)
    | exact superpose eq30596 eq99
    | (have j0 := eq99 X0 X1
       grind)
    | exact resolve eq99 eq30596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq30596
  have eq1474492 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1474491 X0 X1
       have i₂ := eq30812 X0
       grind)
    | exact superpose eq30812 eq1474491
    | (have j0 := eq1474491 X0 X1
       grind)
    | exact resolve eq1474491 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30812 eq1474491
  have eq1475297 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq1474492 X1 X0
       grind)
    | (have i₁ := eq11 X1
       have i₂ := eq1474492 X0 X1
       grind)
    | exact superpose eq1474492 eq11
    | (have j1 := eq1474492 X1 X0
       grind)
    | exact resolve eq11 eq1474492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474492
  have eq1475770 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1475297 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1475297
    | (have j0 := eq1475297 X0 X1
       grind)
    | exact resolve eq1475297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475297
  have eq1478744 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ X0) = (M.op X1 X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1475770 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1475770
    | (have j0 := eq1475770 (σ X0) X1
       grind)
    | exact resolve eq1475770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475770
  have eq1479781 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = (M.op X1 X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1478744 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq1478744
    | (have j0 := eq1478744 X0 X1
       grind)
    | exact resolve eq1478744 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1478744
  have eq1480249 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1479781 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1479781
    | (have j0 := eq1479781 X1 (σ X0)
       grind)
    | exact resolve eq1479781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479781
  have eq1481245 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1480249 X0 X1
       have i₂ := eq30963 X0
       grind)
    | exact superpose eq30963 eq1480249
    | (have j0 := eq1480249 X0 X1
       grind)
    | exact resolve eq1480249 eq30963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480249
  have eq1483872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq135
       have i₂ := eq1481245 x y
       grind)
    | exact superpose eq1481245 eq135
    | (have j1 := eq1481245 x y
       grind)
    | (have r₁ := eq135
       have r₂ := eq1481245 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq135
       have r₂ := eq1481245 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq135 eq1481245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1481245
  have eq1483873 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq1483872
  have eq1484037 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq1483873
       have i₂ := eq30963 x
       grind)
    | exact superpose eq30963 eq1483873
    | exact resolve eq1483873 eq30963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483873
  have eq1484038 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1484037
  have eq1484977 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1484038
       grind)
    | exact superpose eq1484038 eq16
    | exact resolve eq16 eq1484038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484038
  have eq1484978 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1484977
       have r₂ := eq30963 x
       grind)
    | exact resolve eq1484977 eq30963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484977
  have eq1484981 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1484978
       grind)
    | exact superpose eq1484978 eq10
    | exact resolve eq10 eq1484978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484978
  have eq1485906 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1484981
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1484981
    | exact resolve eq1484981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484981
  have eq1485953 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1485906
       grind)
    | exact superpose eq1485906 eq16
    | exact resolve eq16 eq1485906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485906
  have eq1485954 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1485953
       have r₂ := eq30963 x
       grind)
    | exact resolve eq1485953 eq30963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30963 eq1485953
  have eq1486006 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33068 x
       have i₂ := eq1485954
       grind)
    | exact superpose eq1485954 eq33068
    | exact resolve eq33068 eq1485954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33068
  have eq1486103 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1485954
       grind)
    | exact superpose eq1485954 eq10
    | exact resolve eq10 eq1485954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485954
  have eq1487032 : y = (M.op x x) := by
    first
    | (have i₁ := eq1486103
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1486103
    | exact resolve eq1486103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486103
  have eq1487525 : y = (M.op x y) := by
    first
    | (have i₁ := eq1430 x x
       have i₂ := eq1487032
       grind)
    | exact superpose eq1487032 eq1430
    | exact resolve eq1430 eq1487032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430 eq1487032
  have eq1500292 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1486006
       grind)
    | exact superpose eq1486006 eq16
    | exact resolve eq16 eq1486006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486006
  have eq1501445 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1500292
       have i₂ := eq1487525
       grind)
    | exact superpose eq1487525 eq1500292
    | exact resolve eq1500292 eq1487525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487525 eq1500292
  have eq1501446 : False := by grind
  exact eq1501446

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq92
  have eq229 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | (have j0 := eq94 X1 X1
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq256 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq229
    | (have j0 := eq229 X0 X1
       grind)
    | exact resolve eq229 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq229
  have eq262 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq256 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq256 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq256
  have eq266 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq262
  have eq763 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266
    | exact resolve eq266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq1167 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq763 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq763 X0 X1
       grind)
    | exact superpose eq763 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq763 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq763 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq763 X0 X1
       grind)
    | exact resolve eq13 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1253 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1226 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1226 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1994 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq2002 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1994 X0 X1
       have j1 := eq763 X1 X0
       grind)
    | (have r₁ := eq1994 X0 X0
       have r₂ := eq763 X0 X0
       grind)
    | (have r₁ := eq1994 X1 X0
       have r₂ := eq763 X0 X1
       grind)
    | exact resolve eq1994 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq1994
  have eq2053 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2002 (σ X1) (σ X0)
       grind)
    | exact superpose eq2002 eq15
    | exact resolve eq15 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2072 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2053 X0 X1
       have i₂ := eq2002 X1 X0
       grind)
    | exact superpose eq2002 eq2053
    | exact resolve eq2053 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002 eq2053
  have eq2892 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2072 x y
       grind)
    | exact superpose eq2072 eq16
    | (have r₁ := eq16
       have r₂ := eq2072 x y
       grind)
    | exact resolve eq16 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2944 : False := by grind
  exact eq2944

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_x_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
    | (have i₁ := eq39 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq39
    | exact resolve eq39 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq123 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq88
    | (have j0 := eq88 (σ X0)
       grind)
    | exact resolve eq88 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq88 (τ X0)
       grind)
    | exact superpose eq88 eq18
    | (have j1 := eq88 (τ X0)
       grind)
    | exact resolve eq18 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq132 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq129
    | (have j0 := eq129 X0
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq370 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq182 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq182 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq182 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq182 X0 X1
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq182 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq382 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq384 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq382
    | (have j0 := eq382 X0 X1
       grind)
    | exact resolve eq382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq583 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
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
  have eq689 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq123 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq123 X0
       grind)
    | exact resolve eq12 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq713 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq689 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq689 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq689 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq724 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq713 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq713
    | (have j0 := eq713 (τ X0) X1
       grind)
    | exact resolve eq713 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq733 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq740 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq745 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq740 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq740
    | (have j0 := eq740 (τ X0) X1
       grind)
    | exact resolve eq740 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq740
  have eq806 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq10
    | (have j1 := eq132 X0
       grind)
    | exact resolve eq10 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq1964 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (τ X0)
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq67
    | (have j1 := eq806 X0
       grind)
    | exact resolve eq67 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq806
  have eq6483 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       have j1 := eq380 X1 X0
       grind)
    | (have r₁ := eq384 X1 X0
       have r₂ := eq380 X0 X1
       grind)
    | (have r₁ := eq384 X1 X1
       have r₂ := eq380 X1 X1
       grind)
    | exact resolve eq384 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq384
  have eq6484 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6483 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6483
    | exact resolve eq6483 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6513 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6483 y x
       grind)
    | exact superpose eq6483 eq16
    | (have j1 := eq6483 x x
       grind)
    | exact resolve eq16 eq6483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483
  have eq6605 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6484 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq6484
    | (have j0 := eq6484 X0 X1
       grind)
    | exact resolve eq6484 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6484
  have eq6609 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6605 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6605
    | (have j0 := eq6605 X1 X1
       grind)
    | exact resolve eq6605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6605
  have eq7167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6513
       have i₂ := eq6609 y x
       grind)
    | exact superpose eq6609 eq6513
    | (have j1 := eq6609 x (σ x)
       grind)
    | exact resolve eq6513 eq6609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6513 eq6609
  have eq7172 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq7167
  have eq7178 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq7172
       grind)
    | exact superpose eq7172 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq7172
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq7172
       grind)
    | exact resolve eq12 eq7172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7172
  have eq7252 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq7178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7178
  have eq7300 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq745 (σ x) X0
       have i₂ := eq7252 (σ x)
       grind)
    | exact superpose eq7252 eq745
    | (have j0 := eq745 (σ x) X0
       grind)
    | exact resolve eq745 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq7316 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1964 (σ x)
       have i₂ := eq7252 (σ x)
       grind)
    | exact superpose eq7252 eq1964
    | (have j0 := eq1964 (σ x)
       grind)
    | exact resolve eq1964 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq7252
  have eq7346 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq7316
  have eq7352 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq7300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7300
  have eq7372 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7346
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7346
    | exact resolve eq7346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7346
  have eq7373 : x = (M.op x x) := by grind
  clear eq7372
  have eq7377 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7352 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7352
    | exact resolve eq7352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq7385 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq7377 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq7377 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq7377 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7377
  have eq7394 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq7373
       grind)
    | exact superpose eq7373 eq73
    | exact resolve eq73 eq7373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7452 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq583 x x x
       have i₂ := eq7373
       grind)
    | exact superpose eq7373 eq583
    | exact resolve eq583 eq7373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7373
  have eq7464 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq7452 X0
       have i₂ := eq91 x X0
       grind)
    | exact superpose eq91 eq7452
    | exact resolve eq7452 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq7452
  have eq7500 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq711 x
       have i₂ := eq7385 x
       grind)
    | exact superpose eq7385 eq711
    | (have j0 := eq711 x
       grind)
    | exact resolve eq711 eq7385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq7385
  have eq7559 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7500
  have eq8436 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 (σ x) X0
       have i₂ := eq7559
       grind)
    | exact superpose eq7559 eq73
    | exact resolve eq73 eq7559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq7559
  have eq8668 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7394 X0
       have i₂ := eq7464 X0
       grind)
    | exact superpose eq7464 eq7394
    | exact resolve eq7394 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7394 eq7464
  have eq8736 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq583 x X1 X0
       have i₂ := eq8668 X0
       grind)
    | exact superpose eq8668 eq583
    | exact resolve eq583 eq8668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq8817 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8736 X0 X0
       have i₂ := eq8668 X0
       grind)
    | exact superpose eq8668 eq8736
    | exact resolve eq8736 eq8668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8736
  have eq13715 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8436 X0
       have i₂ := eq8817 X0 (σ x)
       grind)
    | exact superpose eq8817 eq8436
    | exact resolve eq8436 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8436 eq8817
  have eq13720 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13715 (σ y)
       grind)
    | exact superpose eq13715 eq16
    | exact resolve eq16 eq13715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13715
  have eq13900 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13720
       have i₂ := eq8668 y
       grind)
    | exact superpose eq8668 eq13720
    | exact resolve eq13720 eq8668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8668 eq13720
  have eq13901 : False := by grind
  exact eq13901

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
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
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq287 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x x
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq9
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq9 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq67
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq67 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq305 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq306 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq310 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq383 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq306 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq306
    | (have j0 := eq306 (τ X0)
       grind)
    | exact resolve eq306 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq393 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq383
    | (have j0 := eq383 X0
       grind)
    | exact resolve eq383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq400 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq393
    | (have j0 := eq393 X0
       grind)
    | exact resolve eq393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq405 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq400 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq400
    | (have j0 := eq400 (τ X0)
       grind)
    | exact resolve eq400 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq679 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
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
  have eq1557 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq310 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1599 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1557 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1557
    | (have j0 := eq1557 X0
       grind)
    | exact resolve eq1557 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1557
  have eq1609 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1599 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1599
    | (have j0 := eq1599 X0
       grind)
    | exact resolve eq1599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq5553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq287
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq287
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq287 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq5556 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5553
  have eq6137 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq288 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq288
    | (have j0 := eq288 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq288 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq288
  have eq6247 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6137 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6137
    | (have j0 := eq6137 X0 X0 X2
       grind)
    | exact resolve eq6137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6137
  have eq6254 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6247 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6247
    | (have j0 := eq6247 X0 X0 X2
       grind)
    | exact resolve eq6247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247
  have eq6255 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6254 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6254
    | (have j0 := eq6254 X0 X0 X2
       grind)
    | exact resolve eq6254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254
  have eq6256 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6255 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6255
    | (have j0 := eq6255 X0 X1 X2
       grind)
    | exact resolve eq6255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6255
  have eq6257 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6256 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6256
    | (have j0 := eq6256 X0 X1 X2
       grind)
    | exact resolve eq6256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq12018 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (k X1 X0) X1 X0
       have i₂ := eq6257 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq6257 eq91
    | (have j1 := eq6257 X1 X1 x
       grind)
    | exact resolve eq91 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq6257
  have eq19396 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5556
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5556
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq5556
       grind)
    | exact resolve eq12 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19516 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19396
  have eq26298 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12018 X0 X0
       have i₂ := eq1609 X0
       grind)
    | exact superpose eq1609 eq12018
    | (have j0 := eq12018 X0 X0
       have j1 := eq1609 X0
       grind)
    | exact resolve eq12018 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609 eq12018
  have eq26432 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26298
  have eq26435 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26432 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26432
    | (have j0 := eq26432 (σ X0)
       grind)
    | exact resolve eq26432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26432
  have eq201702 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ (M.op X1 X1) = (k X1 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq19516 X1
       grind)
    | exact superpose eq19516 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq19516 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq19516 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq19516 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq19516 X0
       grind)
    | exact resolve eq12 eq19516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201982 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq201702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201702
  have eq208093 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq405 (σ y)
       have i₂ := eq201982 X0 (σ y)
       grind)
    | exact superpose eq201982 eq405
    | (have j0 := eq405 (σ y)
       have j1 := eq201982 X0 x
       grind)
    | exact resolve eq405 eq201982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201982
  have eq208492 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208093 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq208093
    | (have j0 := eq208093 X0
       grind)
    | exact resolve eq208093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208093
  have eq208603 : ∀ X0 : G, y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208492 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq208492
    | (have j0 := eq208492 X0
       grind)
    | exact resolve eq208492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208492
  have eq208604 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq208603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208603
  have eq211700 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208604 X0
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq208604
    | (have j0 := eq208604 X0
       grind)
    | exact resolve eq208604 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208604
  have eq211709 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq211700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211700
  have eq211713 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq211709 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq211709 X0
       have r₂ := eq12 X0 y
       grind)
    | (have r₁ := eq211709 X0
       have r₂ := eq12 X0 x
       grind)
    | (have r₁ := eq211709 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq211709 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211709
  have eq211714 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq211713 X0
       grind)
    | (have r₁ := eq211713 X0
       have r₂ := eq10 y
       grind)
    | exact resolve eq211713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211713
  have eq213050 : (τ (M.op (σ x) (σ x))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq405 (σ x)
       have i₂ := eq211714 (σ x)
       grind)
    | exact superpose eq211714 eq405
    | (have j0 := eq405 (σ x)
       grind)
    | exact resolve eq405 eq211714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211714
  have eq213455 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213050
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq213050
    | exact resolve eq213050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213050
  have eq213566 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq213455
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq213455
    | exact resolve eq213455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213455
  have eq213567 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq213566
  have eq215309 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq213567
       have i₂ := eq19516 X0
       grind)
    | exact superpose eq19516 eq213567
    | (have j1 := eq19516 X0
       grind)
    | exact resolve eq213567 eq19516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19516
  have eq215318 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq215309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215309
  have eq215322 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq215318 X0
       grind)
    | (have r₁ := eq215318 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq215318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215318
  have eq216668 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq405 (σ y)
       have i₂ := eq215322 (σ y)
       grind)
    | exact superpose eq215322 eq405
    | (have j0 := eq405 (σ y)
       grind)
    | exact resolve eq405 eq215322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq215322
  have eq217074 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq216668
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq216668
    | exact resolve eq216668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216668
  have eq217185 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq217074
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq217074
    | exact resolve eq217074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217074
  have eq217186 : y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq217185
  have eq217627 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq217186
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq217186
    | exact resolve eq217186 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq217186
  have eq217636 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq217627
  have eq217640 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq217636
       have r₂ := eq10 y
       grind)
    | exact resolve eq217636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217636
  have eq217642 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq213567
       have i₂ := eq217640
       grind)
    | exact superpose eq217640 eq213567
    | exact resolve eq213567 eq217640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213567 eq217640
  have eq217932 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq217642
  have eq218041 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq217932
       have r₂ := eq10 x
       grind)
    | exact resolve eq217932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217932
  have eq218055 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq218041
       grind)
    | exact superpose eq218041 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq218041
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq218041
       grind)
    | exact resolve eq12 eq218041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218060 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq218041
       grind)
    | exact superpose eq218041 eq73
    | exact resolve eq73 eq218041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218202 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq679 y y x
       have i₂ := eq218041
       grind)
    | exact superpose eq218041 eq679
    | exact resolve eq679 eq218041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218343 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq218055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218055
  have eq218398 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq218202 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq218202
    | exact resolve eq218202 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218202
  have eq221301 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq306 y
       have i₂ := eq218343 y
       grind)
    | exact superpose eq218343 eq306
    | (have j0 := eq306 y
       grind)
    | exact resolve eq306 eq218343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq218343
  have eq223958 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq218060 X0
       have i₂ := eq218398 X0
       grind)
    | exact superpose eq218398 eq218060
    | exact resolve eq218060 eq218398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218060 eq218398
  have eq224456 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq223958 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223958
  have eq224495 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq224456 X1
       grind)
    | exact superpose eq224456 eq73
    | (have j1 := eq224456 X1
       grind)
    | exact resolve eq73 eq224456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224637 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq679 x x x
       have i₂ := eq224456 X0
       grind)
    | exact superpose eq224456 eq679
    | (have j1 := eq224456 X1
       grind)
    | exact resolve eq679 eq224456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224456
  have eq224839 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq224637 X0 X1
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq224637
    | (have j0 := eq224637 X0 X1
       grind)
    | exact resolve eq224637 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224637
  have eq231235 : ∀ X0 X1 X2 : G, (M.op y X2) = X2 ∨ (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq224495 X0 X2
       have i₂ := eq224839 X0 X1
       grind)
    | exact superpose eq224839 eq224495
    | (have j0 := eq224495 X0 X2
       have j1 := eq224839 X0 X2
       grind)
    | exact resolve eq224495 eq224839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224495 eq224839
  have eq252633 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq231235 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231235
  have eq252634 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq252633 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252633
  have eq252663 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq252634 y X1
       grind)
    | exact superpose eq252634 eq74
    | (have j1 := eq252634 X0 X1
       grind)
    | exact resolve eq74 eq252634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq253500 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252663 X0 X1
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq252663
    | (have j0 := eq252663 X0 X1
       grind)
    | exact resolve eq252663 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252663
  have eq258389 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq253500 X0 X1
       have i₂ := eq252634 X0 X2
       grind)
    | exact superpose eq252634 eq253500
    | (have j0 := eq253500 X0 X1
       have j1 := eq252634 X0 X1
       grind)
    | exact resolve eq253500 eq252634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252634 eq253500
  have eq309528 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq258389 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258389
  have eq309529 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq309528 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309528
  have eq311627 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq309529 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309529
  have eq311628 : y = (M.op x y) := by grind
  clear eq311627
  have eq1281746 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq221301
       have i₂ := eq218041
       grind)
    | exact superpose eq218041 eq221301
    | exact resolve eq221301 eq218041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218041 eq221301
  have eq1281756 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1281746
  have eq1281757 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1281756
  have eq1281769 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) X0
       have i₂ := eq1281757
       grind)
    | exact superpose eq1281757 eq73
    | exact resolve eq73 eq1281757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281933 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq679 (σ y) (σ y) x
       have i₂ := eq1281757
       grind)
    | exact superpose eq1281757 eq679
    | exact resolve eq679 eq1281757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281757
  have eq1282770 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1281933 X0
       have i₂ := eq94 (σ y) X0
       grind)
    | exact superpose eq94 eq1281933
    | exact resolve eq1281933 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281933
  have eq1382260 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1281769 X0
       have i₂ := eq1282770 X0
       grind)
    | exact superpose eq1282770 eq1281769
    | exact resolve eq1281769 eq1282770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281769
  have eq1383532 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1382260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382260
  have eq1383582 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1282770 X0
       have i₂ := eq1383532 X0
       grind)
    | exact superpose eq1383532 eq1282770
    | exact resolve eq1282770 eq1383532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282770 eq1383532
  have eq1385833 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1383582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383582
  have eq1390244 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1385833 (σ x)
       grind)
    | exact superpose eq1385833 eq16
    | exact resolve eq16 eq1385833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385833
  have eq1390725 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1390244
       have i₂ := eq311628
       grind)
    | exact superpose eq311628 eq1390244
    | exact resolve eq1390244 eq311628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390244
  have eq1390726 : x = (M.op x x) := by grind
  clear eq1390725
  have eq1390902 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1390726
       grind)
    | exact superpose eq1390726 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1390726
       grind)
    | exact resolve eq12 eq1390726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390907 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq1390726
       grind)
    | exact superpose eq1390726 eq73
    | exact resolve eq73 eq1390726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391059 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq679 x x x
       have i₂ := eq1390726
       grind)
    | exact superpose eq1390726 eq679
    | exact resolve eq679 eq1390726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391597 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1390902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390902
  have eq1391840 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1391059 X0
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq1391059
    | exact resolve eq1391059 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1391059
  have eq1392001 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 x) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq1391597 X0
       grind)
    | exact superpose eq1391597 eq73
    | exact resolve eq73 eq1391597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1395886 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26435 x
       have i₂ := eq1391597 x
       grind)
    | exact superpose eq1391597 eq26435
    | (have j0 := eq26435 x
       grind)
    | exact resolve eq26435 eq1391597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26435
  have eq1396335 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1395886
       have i₂ := eq1390726
       grind)
    | exact superpose eq1390726 eq1395886
    | exact resolve eq1395886 eq1390726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390726 eq1395886
  have eq1396336 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1396335
  have eq1396937 : (σ x) = (k (σ x) x) := by
    first
    | (have i₁ := eq1396336
       have i₂ := eq1391597 (σ x)
       grind)
    | exact superpose eq1391597 eq1396336
    | exact resolve eq1396336 eq1391597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391597 eq1396336
  have eq1421371 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1390907 X0
       have i₂ := eq1391840 X0
       grind)
    | exact superpose eq1391840 eq1390907
    | exact resolve eq1390907 eq1391840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390907 eq1391840
  have eq1421727 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq679 x X1 X0
       have i₂ := eq1421371 X0
       grind)
    | exact superpose eq1421371 eq679
    | exact resolve eq679 eq1421371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq1424658 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1421727 X0 X0
       have i₂ := eq1421371 X0
       grind)
    | exact superpose eq1421371 eq1421727
    | exact resolve eq1421727 eq1421371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421371 eq1421727
  have eq1567954 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1392001 (σ x) X0
       have i₂ := eq1396937
       grind)
    | exact superpose eq1396937 eq1392001
    | exact resolve eq1392001 eq1396937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392001 eq1396937
  have eq1569054 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1567954 X0
       have i₂ := eq1424658 X0 (σ x)
       grind)
    | exact superpose eq1424658 eq1567954
    | exact resolve eq1567954 eq1424658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424658 eq1567954
  have eq1574319 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1569054 (σ y)
       grind)
    | exact superpose eq1569054 eq16
    | exact resolve eq16 eq1569054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569054
  have eq1577207 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1574319
       have i₂ := eq311628
       grind)
    | exact superpose eq311628 eq1574319
    | exact resolve eq1574319 eq311628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311628 eq1574319
  have eq1577208 : False := by grind
  exact eq1577208

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq44
    | (have j1 := eq89 x x
       grind)
    | exact resolve eq44 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq89
    | (have j0 := eq89 (σ x) x
       grind)
    | exact resolve eq89 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq700
    | exact resolve eq700 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq704 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq701
       have r₂ := eq27
       grind)
    | exact resolve eq701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq717 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq704 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq704
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq704
       grind)
    | exact resolve eq13 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq747 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq718 eq49
    | exact resolve eq49 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq718
  have eq775 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq704 eq747
    | exact resolve eq747 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq747
  have eq788 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq775
  have eq790 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq788
    | exact resolve eq788 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq788
  have eq793 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89 x x
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq89
    | (have j0 := eq89 x x
       grind)
    | exact resolve eq89 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq794 : x = (M.op x x) := by grind
  clear eq793
  have eq810 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq53
    | exact resolve eq53 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq811 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq50
    | exact resolve eq50 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq812 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq14
    | exact resolve eq14 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq14
    | exact resolve eq14 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq794
       grind)
    | exact resolve eq13 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq853 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq822 x
       grind)
    | exact superpose eq822 eq43
    | exact resolve eq43 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq855 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq822 sF0
       grind)
    | exact superpose eq822 eq121
    | exact resolve eq121 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq822
  have eq861 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq853
       have i₂ := eq794
       grind)
    | exact superpose eq794 eq853
    | exact resolve eq853 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq853
  have eq862 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq861
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq861
    | exact resolve eq861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq867 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq862 eq89
    | (have j0 := eq89 (σ x) x
       grind)
    | exact resolve eq89 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq862
  have eq868 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq867
  have eq897 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq868 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq868
       grind)
    | exact resolve eq13 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq898 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq897 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq955 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq898 eq855
    | exact resolve eq855 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq898
  have eq1041 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq813 (M.op x X0)
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq813
    | exact resolve eq813 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1046 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq810 eq813
    | exact resolve eq813 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1046 eq810
    | exact resolve eq810 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq1046
  have eq1071 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1055 eq955
    | exact resolve eq955 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1072 : y = (M.op x y) := by
    first
    | exact superpose eq1055 eq811
    | exact resolve eq811 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq1055
  have eq1080 : y = (M.op x y) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1072
    | exact resolve eq1072 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1072
  have eq1081 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1071
    | exact resolve eq1071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1071
  have eq1082 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1080 eq20
    | exact resolve eq20 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1080
  have eq1115 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1082
    | exact resolve eq1082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1082
  have eq1118 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1115 eq26
    | exact resolve eq26 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1115
  have eq1223 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq812 X0
       have i₂ := eq1041 X0
       grind)
    | exact superpose eq1041 eq812
    | exact resolve eq812 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq1041
  have eq1340 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq813 X0
       have i₂ := eq1223 X0
       grind)
    | exact superpose eq1223 eq813
    | exact resolve eq813 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1223
  have eq1363 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1340 X0
       grind)
    | exact superpose eq1340 eq14
    | exact resolve eq14 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1383 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1363 X0 X1
       have i₂ := eq1340 X1
       grind)
    | exact superpose eq1340 eq1363
    | exact resolve eq1363 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq1363
  have eq1512 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1081 eq1383
    | exact resolve eq1383 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq1383
  have eq1536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1118 eq1512
    | exact resolve eq1512 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq1512
  have eq1553 : False := by grind
  exact eq1553

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq71
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq71 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq74
    | (have j0 := eq74 (σ y) x
       grind)
    | exact resolve eq74 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq699
    | exact resolve eq699 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq703 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq700
       have r₂ := eq27
       grind)
    | exact resolve eq700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq714 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq703 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq703
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq703
       grind)
    | exact resolve eq13 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq731 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq715 eq84
    | exact resolve eq84 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq715
  have eq771 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq703 eq731
    | exact resolve eq731 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq731
  have eq784 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq771
  have eq786 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq784
    | exact resolve eq784 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq784
  have eq789 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74 y y
       have i₂ := eq786
       grind)
    | exact superpose eq786 eq74
    | (have j0 := eq74 y x
       grind)
    | exact resolve eq74 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq790 : y = (M.op y y) := by grind
  clear eq789
  have eq793 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq14
    | exact resolve eq14 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq14
    | exact resolve eq14 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq790
       grind)
    | exact resolve eq13 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq818 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq803 x
       grind)
    | exact superpose eq803 eq44
    | exact resolve eq44 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq820 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq803 y
       grind)
    | exact superpose eq803 eq72
    | exact resolve eq72 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq803
  have eq827 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq820
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq820
    | exact resolve eq820 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq820
  have eq828 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq827
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq827
    | exact resolve eq827 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq833 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq828 eq74
    | (have j0 := eq74 (σ y) x
       grind)
    | exact resolve eq74 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq828
  have eq834 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq833
  have eq858 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
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
  have eq859 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq889 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq859 eq818
    | exact resolve eq818 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq859
  have eq992 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq794 (M.op y X0)
       have i₂ := eq793 X0
       grind)
    | exact superpose eq793 eq794
    | exact resolve eq794 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq793 X0
       have i₂ := eq992 X0
       grind)
    | exact superpose eq992 eq793
    | exact resolve eq793 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq992
  have eq1056 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq1042 X0
       grind)
    | exact superpose eq1042 eq794
    | exact resolve eq794 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq1064 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1042 X0
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq1042
    | exact resolve eq1042 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1070 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq889
       have i₂ := eq1056 x
       grind)
    | exact superpose eq1056 eq889
    | exact resolve eq889 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1074 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y X0
       have i₂ := eq1056 X0
       grind)
    | exact superpose eq1056 eq14
    | exact resolve eq14 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1074 X0 X1
       have i₂ := eq1056 X1
       grind)
    | exact superpose eq1056 eq1074
    | exact resolve eq1074 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq1074
  have eq1097 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1070
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1070
    | exact resolve eq1070 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1070
  have eq1098 : y = (M.op x y) := by
    first
    | (have i₁ := eq1064 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1064
    | (have j0 := eq1064 x
       grind)
    | exact resolve eq1064 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1064
  have eq1161 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1098 eq20
    | exact resolve eq20 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1098
  have eq1194 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1161
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1161
    | exact resolve eq1161 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1161
  have eq1206 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1194 eq26
    | exact resolve eq26 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1243 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1194 eq1097
    | exact resolve eq1097 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq1194
  have eq1422 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1243 eq1094
    | exact resolve eq1094 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1243
  have eq1448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1206 eq1422
    | exact resolve eq1422 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq1422
  have eq1460 : False := by grind
  exact eq1460

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq67 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq61
    | exact resolve eq61 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq61
    | exact resolve eq61 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq81 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq135 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X0 X2 X3
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq62
    | exact resolve eq62 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq368 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq9
    | (have j1 := eq70 X0 X0
       grind)
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq67
    | (have j1 := eq70 X0 X0
       grind)
    | exact resolve eq67 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq70
  have eq391 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq468 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1316 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq391 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq391
    | exact resolve eq391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq1350 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1316 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1316
    | (have j0 := eq1316 X0
       grind)
    | exact resolve eq1316 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1316
  have eq1354 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1350 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1350
    | (have j0 := eq1350 X0
       grind)
    | exact resolve eq1350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1361 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1354 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1354
    | (have j0 := eq1354 (τ X0)
       grind)
    | exact resolve eq1354 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq368
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq368
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq368 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq5646 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5643
  have eq6234 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq369 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq369
    | (have j0 := eq369 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq369 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq369
  have eq6359 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6234 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6234
    | (have j0 := eq6234 X0 X0 X2
       grind)
    | exact resolve eq6234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6234
  have eq6370 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6359 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6359
    | (have j0 := eq6359 X0 X0 X2
       grind)
    | exact resolve eq6359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq6379 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6370 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6370
    | (have j0 := eq6370 X0 X0 X2
       grind)
    | exact resolve eq6370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6370
  have eq6388 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6379 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6379
    | (have j0 := eq6379 X0 X1 X2
       grind)
    | exact resolve eq6379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6393 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6388 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6388
    | (have j0 := eq6388 X0 X1 X2
       grind)
    | exact resolve eq6388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6388
  have eq11113 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (k X1 X0) X1 X0
       have i₂ := eq6393 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq6393 eq91
    | (have j1 := eq6393 X1 X1 x
       grind)
    | exact resolve eq91 eq6393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq6393
  have eq18788 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5646
       grind)
    | exact superpose eq5646 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5646
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5646
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq5646
       grind)
    | exact resolve eq12 eq5646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646
  have eq18907 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq18788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18788
  have eq24814 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11113 X0 X0
       have i₂ := eq1354 X0
       grind)
    | exact superpose eq1354 eq11113
    | (have j0 := eq11113 X0 X0
       have j1 := eq1354 X0
       grind)
    | exact resolve eq11113 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354 eq11113
  have eq24936 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24814
  have eq24939 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24936 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq24936
    | (have j0 := eq24936 (σ X0)
       grind)
    | exact resolve eq24936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24936
  have eq143374 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ (σ y) = (k X1 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq18907 X0
       grind)
    | exact superpose eq18907 eq12
    | (have j1 := eq18907 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq18907 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq18907 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq18907 X0
       grind)
    | exact resolve eq12 eq18907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18907
  have eq143628 : ∀ X0 X1 : G, (σ y) = (k X1 (σ y)) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq143374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143374
  have eq143780 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1361 (σ y)
       have i₂ := eq143628 X0 (σ y)
       grind)
    | exact superpose eq143628 eq1361
    | (have j0 := eq1361 (σ y)
       have j1 := eq143628 X0 x
       grind)
    | exact resolve eq1361 eq143628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143628
  have eq144013 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq143780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143780
  have eq144094 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq144013 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq144013
    | (have j0 := eq144013 X0
       grind)
    | exact resolve eq144013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144013
  have eq144095 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq144094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144094
  have eq144214 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1361 (σ x)
       have i₂ := eq144095 (σ x)
       grind)
    | exact superpose eq144095 eq1361
    | (have j0 := eq1361 (σ x)
       grind)
    | exact resolve eq1361 eq144095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361 eq144095
  have eq144447 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq144214
  have eq144528 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq144447
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq144447
    | exact resolve eq144447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144447
  have eq144529 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq144528
  have eq144601 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq144529
       grind)
    | exact superpose eq144529 eq12
    | (have r₁ := eq12 X0 y
       have r₂ := eq144529
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq144529
       grind)
    | exact resolve eq12 eq144529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144606 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 y X0
       have i₂ := eq144529
       grind)
    | exact superpose eq144529 eq81
    | exact resolve eq81 eq144529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144693 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq468 y y x
       have i₂ := eq144529
       grind)
    | exact superpose eq144529 eq468
    | exact resolve eq468 eq144529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144529
  have eq144855 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq144601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144601
  have eq144917 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq144693 X0
       have i₂ := eq113 y X0
       grind)
    | exact superpose eq113 eq144693
    | exact resolve eq144693 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144693
  have eq145016 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24939 y
       have i₂ := eq144855 y
       grind)
    | exact superpose eq144855 eq24939
    | (have j0 := eq24939 y
       grind)
    | exact resolve eq24939 eq144855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144855
  have eq145196 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq145016
  have eq147370 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 (σ y) X0
       have i₂ := eq145196
       grind)
    | exact superpose eq145196 eq81
    | exact resolve eq81 eq145196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145196
  have eq147733 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq144606 X0
       have i₂ := eq144917 X0
       grind)
    | exact superpose eq144917 eq144606
    | exact resolve eq144606 eq144917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144606 eq144917
  have eq148172 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq147733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147733
  have eq148209 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 x X0
       have i₂ := eq148172 X1
       grind)
    | exact superpose eq148172 eq81
    | (have j1 := eq148172 X1
       grind)
    | exact resolve eq81 eq148172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148296 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq468 x x x
       have i₂ := eq148172 X0
       grind)
    | exact superpose eq148172 eq468
    | (have j1 := eq148172 X1
       grind)
    | exact resolve eq468 eq148172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148172
  have eq148520 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148296 X0 X1
       have i₂ := eq113 x X0
       grind)
    | exact superpose eq113 eq148296
    | (have j0 := eq148296 X0 X1
       grind)
    | exact resolve eq148296 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148296
  have eq152223 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148209 X0 X1
       have i₂ := eq148520 X0 X2
       grind)
    | exact superpose eq148520 eq148209
    | (have j0 := eq148209 X0 X1
       have j1 := eq148520 X0 X1
       grind)
    | exact resolve eq148209 eq148520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148209 eq148520
  have eq152662 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq152223 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152223
  have eq152702 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 y X0
       have i₂ := eq152662 y X1
       grind)
    | exact superpose eq152662 eq82
    | (have j1 := eq152662 X0 X1
       grind)
    | exact resolve eq82 eq152662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq152744 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 y X1
       have i₂ := eq152662 X0 X2
       grind)
    | exact superpose eq152662 eq9
    | (have j1 := eq152662 X0 X2
       grind)
    | exact resolve eq9 eq152662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153385 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152702 X0 X1
       have i₂ := eq113 y X0
       grind)
    | exact superpose eq113 eq152702
    | (have j0 := eq152702 X0 X1
       grind)
    | exact resolve eq152702 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152702
  have eq157414 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153385 X0 X1
       have i₂ := eq152662 X0 X2
       grind)
    | exact superpose eq152662 eq153385
    | (have j0 := eq153385 X0 X1
       have j1 := eq152662 X0 X1
       grind)
    | exact resolve eq153385 eq152662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153385
  have eq157989 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq157414 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157414
  have eq159360 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq157989 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157989
  have eq159361 : y = (M.op x y) := by grind
  clear eq159360
  have eq182480 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 ∨ (M.op x X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq152744 X1 X0 X2
       have i₂ := eq152662 X0 X3
       grind)
    | exact superpose eq152662 eq152744
    | (have j0 := eq152744 X0 X1 X2
       have j1 := eq152662 X0 X2
       grind)
    | exact resolve eq152744 eq152662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152662 eq152744
  have eq183502 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq182480 X2 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182480
  have eq261421 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147370 X0
       have i₂ := eq183502 X1 (σ y) X0
       grind)
    | exact superpose eq183502 eq147370
    | (have j1 := eq183502 x X1 x
       grind)
    | exact resolve eq147370 eq183502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147370
  have eq261992 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq261421 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261421
  have eq262449 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq183502 X1 (σ y) X0
       have i₂ := eq261992 X0
       grind)
    | exact superpose eq261992 eq183502
    | (have j0 := eq183502 X1 X1 x
       grind)
    | exact resolve eq183502 eq261992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183502 eq261992
  have eq262943 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq262449 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262449
  have eq264605 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262943 (σ x)
       grind)
    | exact superpose eq262943 eq16
    | exact resolve eq16 eq262943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262943
  have eq264849 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq264605
       have i₂ := eq159361
       grind)
    | exact superpose eq159361 eq264605
    | exact resolve eq264605 eq159361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264605
  have eq264850 : x = (M.op x x) := by grind
  clear eq264849
  have eq264881 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq264850
       grind)
    | exact superpose eq264850 eq12
    | (have r₁ := eq12 X0 x
       have r₂ := eq264850
       grind)
    | exact resolve eq12 eq264850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264886 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81 x X0
       have i₂ := eq264850
       grind)
    | exact superpose eq264850 eq81
    | exact resolve eq81 eq264850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq264973 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq468 x x x
       have i₂ := eq264850
       grind)
    | exact superpose eq264850 eq468
    | exact resolve eq468 eq264850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264850
  have eq265202 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq264881 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264881
  have eq265298 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq264973 X0
       have i₂ := eq113 x X0
       grind)
    | exact superpose eq113 eq264973
    | exact resolve eq264973 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq264973
  have eq265409 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24939 x
       have i₂ := eq265202 x
       grind)
    | exact superpose eq265202 eq24939
    | (have j0 := eq24939 x
       grind)
    | exact resolve eq24939 eq265202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24939 eq265202
  have eq265600 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq265409
  have eq273137 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq264886 X0
       have i₂ := eq265298 X0
       grind)
    | exact superpose eq265298 eq264886
    | exact resolve eq264886 eq265298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264886 eq265298
  have eq273250 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x X1) X0) X2) (M.op x X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135 x X1 X0 X2
       have i₂ := eq273137 X0
       grind)
    | exact superpose eq273137 eq135
    | exact resolve eq135 eq273137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq273255 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq468 x X1 X0
       have i₂ := eq273137 X0
       grind)
    | exact superpose eq273137 eq468
    | exact resolve eq468 eq273137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq274449 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq273255 X0 X0
       have i₂ := eq273137 X0
       grind)
    | exact superpose eq273137 eq273255
    | exact resolve eq273255 eq273137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273255
  have eq274451 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq273250 X0 X0 X2
       have i₂ := eq273137 X0
       grind)
    | exact superpose eq273137 eq273250
    | exact resolve eq273250 eq273137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273137 eq273250
  have eq335847 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq274451 (σ x) (σ x) X0
       have i₂ := eq265600
       grind)
    | exact superpose eq265600 eq274451
    | exact resolve eq274451 eq265600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265600 eq274451
  have eq337435 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq335847 X0
       have i₂ := eq274449 X0 (σ x)
       grind)
    | exact superpose eq274449 eq335847
    | exact resolve eq335847 eq274449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274449 eq335847
  have eq338781 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337435 (σ y)
       grind)
    | exact superpose eq337435 eq16
    | exact resolve eq16 eq337435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337435
  have eq339953 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq338781
       have i₂ := eq159361
       grind)
    | exact superpose eq159361 eq338781
    | exact resolve eq338781 eq159361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159361 eq338781
  have eq339954 : False := by grind
  exact eq339954
