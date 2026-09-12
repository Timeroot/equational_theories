import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_y_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
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
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq17
  have eq80 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq43
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq43 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq86 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X0)) = (k X1 (τ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq33 X0 (σ X1)
       grind)
    | exact superpose eq33 eq40
    | exact resolve eq40 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq40
  have eq255 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq263 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq265 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq264 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq280 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq265
    | (have j0 := eq265 (τ X0)
       grind)
    | exact resolve eq265 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq265
  have eq284 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X0
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq287 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq284
    | (have j0 := eq284 X0
       grind)
    | exact resolve eq284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq519 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq287 (τ (M.op (M.op X0 X0) X0))
       have i₂ := eq86 X0 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq86 eq287
    | (have j0 := eq287 (τ (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq287 (τ (M.op (M.op X0 X0) X0))
       have r₂ := eq86 X0 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq287 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq287
  have eq533 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq682 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq724 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq682
    | (have j0 := eq682 X0 X1
       grind)
    | exact resolve eq682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1031 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq255
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq255
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq255 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1032 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1031
  have eq11367 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq533 X0
       grind)
    | exact superpose eq533 eq19
    | exact resolve eq19 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11441 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11367 X0 X1
       have i₂ := eq533 X0
       grind)
    | exact superpose eq533 eq11367
    | exact resolve eq11367 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq11367
  have eq11511 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1032
       grind)
    | exact superpose eq1032 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1032
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1032
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1032
       grind)
    | exact resolve eq13 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq11530 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11511
  have eq11531 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11530
  have eq280667 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq280669 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq280667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280667
  have eq280676 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq280669 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280669
    | exact resolve eq280669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280669
  have eq280861 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq280676 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq280676
    | (have j0 := eq280676 X0
       grind)
    | exact resolve eq280676 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq280676
  have eq280864 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq280861 X0
       have j1 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq280861 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq280861 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280861
  have eq280867 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq280864 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280864
    | exact resolve eq280864 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280864
  have eq281145 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq263 X0 X0
       have i₂ := eq280867 X0
       grind)
    | exact superpose eq280867 eq263
    | (have j0 := eq263 X0 X0
       grind)
    | exact resolve eq263 eq280867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq280867 (σ X0)
       grind)
    | exact superpose eq280867 eq15
    | exact resolve eq15 eq280867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281504 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq281145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281145
  have eq281596 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281385 X0
       have i₂ := eq280867 X0
       grind)
    | exact superpose eq280867 eq281385
    | exact resolve eq281385 eq280867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280867 eq281385
  have eq284458 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X1
       have i₂ := eq281596 X0
       grind)
    | exact superpose eq281596 eq19
    | exact resolve eq19 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq284517 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11441 (σ X0) X1
       have i₂ := eq281596 X0
       grind)
    | exact superpose eq281596 eq11441
    | exact resolve eq11441 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11441
  have eq292688 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq263 x y
       have i₂ := eq11531
       grind)
    | exact superpose eq11531 eq263
    | (have j0 := eq263 x y
       grind)
    | exact resolve eq263 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq11531
  have eq292710 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq292688
  have eq292711 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq292710
  have eq292720 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq292711
       have i₂ := eq281596 x
       grind)
    | exact superpose eq281596 eq292711
    | exact resolve eq292711 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292711
  have eq852770 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq292720
       grind)
    | exact superpose eq292720 eq16
    | exact resolve eq16 eq292720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852774 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq292720
       grind)
    | exact superpose eq292720 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq292720
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq292720
       grind)
    | exact resolve eq13 eq292720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292720
  have eq852824 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq852774
  have eq852831 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq281504 x
       grind)
    | (have r₁ := eq852824
       have r₂ := eq281504 x
       grind)
    | exact resolve eq852824 eq281504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852824
  have eq852832 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq852831
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq852831
    | exact resolve eq852831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852831
  have eq852833 : x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq852832
       have i₂ := eq281596 x
       grind)
    | exact superpose eq281596 eq852832
    | exact resolve eq852832 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852832
  have eq855571 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq281504 x
       have i₂ := eq852833
       grind)
    | exact superpose eq852833 eq281504
    | (have j0 := eq281504 x
       grind)
    | (have r₁ := eq281504 x
       have r₂ := eq852833
       grind)
    | exact resolve eq281504 eq852833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852833
  have eq855754 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq855571
  have eq855853 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have j1 := eq281504 x
       grind)
    | (have r₁ := eq855754
       have r₂ := eq281504 x
       grind)
    | exact resolve eq855754 eq281504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855754
  have eq855943 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq855853
       have i₂ := eq281596 x
       grind)
    | exact superpose eq281596 eq855853
    | exact resolve eq855853 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855853
  have eq855998 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq724 y x
       have i₂ := eq855943
       grind)
    | exact superpose eq855943 eq724
    | (have j0 := eq724 y x
       grind)
    | exact resolve eq724 eq855943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq855943
  have eq856636 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq855998
       have r₂ := eq852770
       grind)
    | exact resolve eq855998 eq852770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855998
  have eq862480 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq852770
       have i₂ := eq856636
       grind)
    | exact superpose eq856636 eq852770
    | exact resolve eq852770 eq856636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852770 eq856636
  have eq862534 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq862480
  have eq862535 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq862534
  have eq865312 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq281504 x
       have i₂ := eq862535
       grind)
    | exact superpose eq862535 eq281504
    | (have j0 := eq281504 x
       grind)
    | (have r₁ := eq281504 x
       have r₂ := eq862535
       grind)
    | exact resolve eq281504 eq862535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862535
  have eq865495 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq865312
  have eq865594 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq281504 x
       grind)
    | (have r₁ := eq865495
       have r₂ := eq281504 x
       grind)
    | exact resolve eq865495 eq281504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281504 eq865495
  have eq865684 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq865594
       have i₂ := eq281596 x
       grind)
    | exact superpose eq281596 eq865594
    | exact resolve eq865594 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865594
  have eq865753 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq284458 x X0
       have i₂ := eq865684
       grind)
    | exact superpose eq865684 eq284458
    | exact resolve eq284458 eq865684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284458
  have eq865765 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq284517 x X0
       have i₂ := eq865684
       grind)
    | exact superpose eq865684 eq284517
    | exact resolve eq284517 eq865684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284517
  have eq865818 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq865684
       grind)
    | exact superpose eq865684 eq10
    | exact resolve eq10 eq865684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866453 : x = (M.op x x) := by
    first
    | (have i₁ := eq865818
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq865818
    | exact resolve eq865818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865818
  have eq866490 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq865765 X0
       have i₂ := eq281596 x
       grind)
    | exact superpose eq281596 eq865765
    | exact resolve eq865765 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865765
  have eq866502 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq865753 X0
       have i₂ := eq281596 x
       grind)
    | exact superpose eq281596 eq865753
    | exact resolve eq865753 eq281596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281596 eq865753
  have eq866589 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq866490 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq866490
    | exact resolve eq866490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866490
  have eq866601 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq866502 X0
       have i₂ := eq865684
       grind)
    | exact superpose eq865684 eq866502
    | exact resolve eq866502 eq865684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865684 eq866502
  have eq866663 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq866589 X0
       have i₂ := eq866453
       grind)
    | exact superpose eq866453 eq866589
    | exact resolve eq866589 eq866453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866453 eq866589
  have eq874818 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq866601 (σ y)
       grind)
    | exact superpose eq866601 eq16
    | exact resolve eq16 eq866601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866601
  have eq875663 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq874818
       have i₂ := eq866663 y
       grind)
    | exact superpose eq866663 eq874818
    | exact resolve eq874818 eq866663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866663 eq874818
  have eq875664 : False := by grind
  exact eq875664

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
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
  clear eq44
  have eq53 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq50
    | exact resolve eq50 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq80 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq79
    | exact resolve eq79 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq77
    | exact resolve eq77 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq77
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq420 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq53
    | exact resolve eq53 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq420 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq53 eq420
    | exact resolve eq420 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1098 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1028 X0 X1
       have i₂ := eq82 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq82 eq1028
    | exact resolve eq1028 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1028
  have eq1110 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1098 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq1098 X0 X1
       have i₂ := eq53 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq53 eq1098
    | exact resolve eq1098 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq24919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq24920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq24919
    | exact resolve eq24919 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24919
  have eq24931 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24920
       have r₂ := eq28
       grind)
    | exact resolve eq24920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24920
  have eq24935 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq24931 eq80
    | exact resolve eq80 eq24931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24931
  have eq25007 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq24935
    | exact resolve eq24935 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24935
  have eq25008 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25007
  have eq25022 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq25008
       grind)
    | exact superpose eq25008 eq53
    | exact resolve eq53 eq25008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25008
  have eq25294 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq25022 x
       grind)
    | exact superpose eq25022 eq53
    | exact resolve eq53 eq25022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq25302 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1110 x X0
       have i₂ := eq25022 x
       grind)
    | exact superpose eq25022 eq1110
    | exact resolve eq1110 eq25022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq25022
  have eq25446 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25302 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25302
    | (have j0 := eq25302 X0
       grind)
    | exact resolve eq25302 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25302
  have eq25451 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq25294 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25294
    | (have j0 := eq25294 y
       grind)
    | exact resolve eq25294 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25294
  have eq25615 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25451 eq30
    | exact resolve eq30 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25451
  have eq25733 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq25615
    | exact resolve eq25615 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25615
  have eq25734 : y = (M.op x y) ∨ x = y := by grind
  clear eq25733
  have eq25895 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25734 eq21
    | exact resolve eq21 eq25734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25734
  have eq26008 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25895
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25895
    | exact resolve eq25895 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25895
  have eq26024 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq26008 eq27
    | exact resolve eq27 eq26008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26008
  have eq28253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25446 eq26024
    | exact resolve eq26024 eq25446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25446 eq26024
  have eq28363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq28253
  have eq28409 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq28363
       have r₂ := eq28
       grind)
    | exact resolve eq28363 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28363
  have eq28418 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq28409 eq30
    | exact resolve eq30 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28409
  have eq28565 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28418
    | exact resolve eq28418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28418
  have eq28566 : x = y := by grind
  clear eq28565
  have eq28582 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq28566
       grind)
    | exact superpose eq28566 eq19
    | exact resolve eq19 eq28566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28583 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28566
       grind)
    | exact superpose eq28566 eq25
    | exact resolve eq25 eq28566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28566
  have eq28696 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28583
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28583
    | exact resolve eq28583 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28583
  have eq28712 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28696 eq27
    | exact resolve eq27 eq28696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28696
  have eq28976 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28712 eq80
    | exact resolve eq80 eq28712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq28712
  have eq29044 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28976
       have i₂ := eq28582
       grind)
    | exact superpose eq28582 eq28976
    | exact resolve eq28976 eq28582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28582 eq28976
  have eq29051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29044 eq15
    | exact resolve eq15 eq29044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29044
  have eq29100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq29051
    | exact resolve eq29051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29051
  have eq29109 : False := by grind
  exact eq29109

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pyy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq42 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq29
    | exact resolve eq29 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq62 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq62 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq62 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq84 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq77 (τ X0) X1
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 (τ X0) X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq101 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X0)) = (k X1 (τ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq72 X0 (σ X1)
       grind)
    | exact superpose eq72 eq29
    | exact resolve eq29 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq72 X0 (τ X1)
       grind)
    | exact superpose eq72 eq18
    | exact resolve eq18 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 (M.op (M.op X0 X0) X1) X1
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq165 : ∀ X0 X1 X2 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq77 (σ X0) X2
       grind)
    | exact superpose eq77 eq22
    | (have j1 := eq77 (σ X0) X2
       grind)
    | exact resolve eq22 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq165
    | (have j0 := eq165 X0 X1 X2
       grind)
    | exact resolve eq165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq437 : ∀ X0 X1 : G, (τ (τ (M.op (M.op X0 X0) X0))) = (k X1 (τ (τ (M.op (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ (M.op (M.op X0 X0) X0))
       have i₂ := eq101 X0 (σ X1)
       grind)
    | exact superpose eq101 eq29
    | exact resolve eq29 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq12
    | (have j1 := eq126 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq126 X0
       grind)
    | exact resolve eq12 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq62
    | (have j1 := eq126 X0
       grind)
    | exact resolve eq62 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq508 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq528 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq508 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq735 : ∀ X0 X1 X2 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 X0) X1
       have i₂ := eq711 X0 X2
       grind)
    | exact superpose eq711 eq29
    | (have j1 := eq711 X0 X2
       grind)
    | exact resolve eq29 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 X0 X1 X2
       have i₂ := eq29 (M.op X0 X0) X1
       grind)
    | exact superpose eq29 eq735
    | (have j0 := eq735 X0 X1 X2
       grind)
    | exact resolve eq735 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq772 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq124 X1 X1 X2
       grind)
    | exact superpose eq124 eq102
    | (have j1 := eq124 X0 X1 X2
       grind)
    | exact resolve eq102 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X1 X1
       have i₂ := eq124 X1 X1 X2
       grind)
    | exact superpose eq124 eq101
    | (have j1 := eq124 X0 X1 X2
       grind)
    | exact resolve eq101 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq124 X0 X0 X2
       grind)
    | exact superpose eq124 eq62
    | (have j1 := eq124 X0 X1 X2
       grind)
    | exact resolve eq62 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1070 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X1 X0)) ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq772 X0 (σ X1) X2
       grind)
    | exact superpose eq772 eq15
    | (have j1 := eq772 X0 X1 X2
       grind)
    | exact resolve eq15 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1098 : ∀ X0 X1 X2 : G, (k X2 (σ X0)) = (M.op (σ X0) X2) ∨ (σ X0) = X2 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq773 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq773
    | (have j0 := eq773 (σ X0) X1 X2
       grind)
    | exact resolve eq773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq1249 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq502
  have eq1285 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1322 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1285 (σ X0) X1
       grind)
    | exact superpose eq1285 eq15
    | (have j1 := eq1285 (σ X0) X1
       grind)
    | exact resolve eq15 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq1285 (τ X0) X1
       grind)
    | exact superpose eq1285 eq18
    | (have j1 := eq1285 (τ X0) X1
       grind)
    | exact resolve eq18 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1334 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1329
    | (have j0 := eq1329 X0 X1
       grind)
    | exact resolve eq1329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1380 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1322 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1393 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1380 (M.op (M.op X0 X0) X0)
       have i₂ := eq72 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq72 eq1380
    | (have j0 := eq1380 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq1380 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) ≠ (σ (σ (M.op (M.op X0 X0) X0))) ∨ (σ (σ (M.op (M.op X0 X0) X0))) = (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1380 (σ (M.op (M.op X0 X0) X0))
       have i₂ := eq102 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq102 eq1380
    | (have j0 := eq1380 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq1380 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : ∀ X0 : G, (σ (τ (τ (M.op (M.op X0 X0) X0)))) ≠ (σ (τ (τ (M.op (M.op X0 X0) X0)))) ∨ (σ (τ (τ (M.op (M.op X0 X0) X0)))) = (M.op (σ (τ (τ (M.op (M.op X0 X0) X0)))) (σ (τ (τ (M.op (M.op X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq1380 (τ (τ (M.op (M.op X0 X0) X0)))
       have i₂ := eq437 X0 (τ (τ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq437 eq1380
    | (have j0 := eq1380 (τ (τ (M.op (M.op X0 X0) X0)))
       grind)
    | exact resolve eq1380 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq1402 : ∀ X0 : G, (σ (σ (k X0 X0))) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1380 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1380
    | (have j0 := eq1380 (σ X0)
       grind)
    | exact resolve eq1380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1405 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1380 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1380
    | (have j0 := eq1380 (τ X0)
       grind)
    | exact resolve eq1380 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1380 X0
       have i₂ := eq1070 X0 X0 X1
       grind)
    | exact superpose eq1070 eq1380
    | (have j0 := eq1380 X0
       have j1 := eq1070 X0 X1 X1
       grind)
    | (have r₁ := eq1380 X1
       have r₂ := eq1070 X1 X1 x
       grind)
    | (have r₁ := eq1380 X0
       have r₂ := eq1070 (σ X0) X1 (σ (k X0 X0))
       grind)
    | (have r₁ := eq1380 X0
       have r₂ := eq1070 (σ (k X0 X0)) X1 (σ X0)
       grind)
    | exact resolve eq1380 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1380
  have eq1408 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1410 : ∀ X0 : G, (σ (τ (τ (M.op (M.op X0 X0) X0)))) = (M.op (σ (τ (τ (M.op (M.op X0 X0) X0)))) (σ (τ (τ (M.op (M.op X0 X0) X0))))) := by
    intro X0
    first
    | (have j0 := eq1400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1414 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) = (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have j0 := eq1396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1417 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq1393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1418 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1405 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1405
    | (have j0 := eq1405 X0
       grind)
    | exact resolve eq1405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1422 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1410 X0
       have i₂ := eq11 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq11 eq1410
    | exact resolve eq1410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1424 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1418 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1418
    | (have j0 := eq1418 X0
       grind)
    | exact resolve eq1418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1441 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1424 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1424
    | (have j0 := eq1424 (τ X0)
       grind)
    | exact resolve eq1424 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : ∀ X0 : G, (τ (τ (k X0 X0))) ≠ (τ (τ X0)) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1441 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1441
    | (have j0 := eq1441 (τ X0)
       grind)
    | exact resolve eq1441 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1549 : ∀ X0 X1 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1334 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1334
    | exact resolve eq1334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1587 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1549 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1549
    | (have j0 := eq1549 X0 X1
       grind)
    | exact resolve eq1549 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1618 : ∀ X0 X1 X2 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X0 X0) X1
       have i₂ := eq1587 X0 X2
       grind)
    | exact superpose eq1587 eq29
    | (have j1 := eq1587 X0 X2
       grind)
    | exact resolve eq29 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1631 : ∀ X0 X1 X2 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1618 X0 X1 X2
       have i₂ := eq29 (M.op X0 X0) X1
       grind)
    | exact superpose eq29 eq1618
    | (have j0 := eq1618 X0 X1 X2
       grind)
    | exact resolve eq1618 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1618
  have eq2524 : ∀ X0 X1 X2 : G, (k (σ (k X0 X0)) X1) = (σ (k (M.op X0 X0) (τ X1))) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X0)
       have i₂ := eq745 X0 X1 X2
       grind)
    | exact superpose eq745 eq19
    | (have j1 := eq745 X0 X1 X2
       grind)
    | exact resolve eq19 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq2533 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (k (σ (k X0 X0)) X1) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2524 X0 X1 X2
       have i₂ := eq19 X1 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq2524
    | (have j0 := eq2524 X0 X1 X2
       grind)
    | exact resolve eq2524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524
  have eq3771 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1098 X0 X2 (σ X1)
       grind)
    | exact superpose eq1098 eq15
    | (have j1 := eq1098 X0 X2 (σ X1)
       grind)
    | exact resolve eq15 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq3952 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (k (σ (k X0 X0)) X2) = (k (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq2533 X0 X2 (τ X1)
       grind)
    | exact superpose eq2533 eq18
    | (have j1 := eq2533 (σ X0) X1 X1
       grind)
    | exact resolve eq18 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3964 : ∀ X0 : G, (k (σ (M.op X0 X0)) X0) ≠ X0 ∨ (k (σ (k X0 X0)) X0) = (k (σ (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq2533 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3969 : ∀ X0 : G, (k (σ (k X0 X0)) X0) = (k (σ (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq3964 X0
       have j1 := eq2533 X0 X0 x
       grind)
    | (have r₁ := eq3964 X0
       have r₂ := eq2533 X0 x (σ (M.op X0 X0))
       grind)
    | exact resolve eq3964 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533 eq3964
  have eq5441 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ X0)) X1) = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) X1
       have i₂ := eq1408 X0 X2
       grind)
    | exact superpose eq1408 eq62
    | (have j1 := eq1408 X0 X2
       grind)
    | exact resolve eq62 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq5567 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X2 ∨ (k (k X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1631 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1631
    | (have j0 := eq1631 X1 X1 X2
       grind)
    | exact resolve eq1631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq5623 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (k (M.op X0 X0) X2) = (k (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq5567 X2 X0 X0
       grind)
    | exact superpose eq5567 eq62
    | (have j1 := eq5567 X0 (M.op X0 X0) X1
       grind)
    | exact resolve eq62 eq5567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq8681 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (M.op X0 X0) X2) = (k (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X1 X1
       have i₂ := eq5623 X1 X1 X2
       grind)
    | exact superpose eq5623 eq101
    | (have j1 := eq5623 X0 X1 X2
       grind)
    | exact resolve eq101 eq5623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq5623
  have eq9483 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k (k (σ X0) (σ X0)) X2) = (k (M.op (σ X0) (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8681 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8681
    | (have j0 := eq8681 (σ X0) X1 X2
       grind)
    | exact resolve eq8681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8681
  have eq9624 : ∀ X0 X1 X2 : G, (k (σ (k X0 X0)) X2) = (k (M.op (σ X0) (σ X0)) X2) ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9483 X0 X1 X2
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9483
    | (have j0 := eq9483 X0 X1 X2
       grind)
    | exact resolve eq9483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq16384 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) X1
       have i₂ := eq5441 X0 (σ X0) X2
       grind)
    | exact superpose eq5441 eq62
    | (have j1 := eq5441 X0 X1 X2
       grind)
    | exact resolve eq62 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441
  have eq16497 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ x = X0 ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq16384 x (σ y) X0
       grind)
    | exact superpose eq16384 eq16
    | (have j1 := eq16384 x x X0
       grind)
    | (have r₁ := eq16
       have r₂ := eq16384 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq16384 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq16 eq16384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16384
  have eq16553 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ x = X1 ∨ (k X1 x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16497 X0
       have i₂ := eq775 x y X1
       grind)
    | exact superpose eq775 eq16497
    | (have j0 := eq16497 X0
       have j1 := eq775 x X1 X0
       grind)
    | (have r₁ := eq16497 X0
       have r₂ := eq775 (σ (M.op x y)) X1 (σ y)
       grind)
    | (have r₁ := eq16497 X0
       have r₂ := eq775 (σ y) X1 (σ (M.op x y))
       grind)
    | exact resolve eq16497 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq16497
  have eq16570 : ∀ X0 X1 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ x = X1 ∨ (k X1 x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have j0 := eq16553 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16553
  have eq19211 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X0) (σ X0))) X1) = (τ (k (σ (k X0 X0)) (σ X1))) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X1
       have i₂ := eq9624 X0 X2 (σ X1)
       grind)
    | exact superpose eq9624 eq23
    | (have j1 := eq9624 X0 X2 X2
       grind)
    | exact resolve eq23 eq9624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9624
  have eq19262 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X0) (σ X0))) X1) = (k (τ (σ (k X0 X0))) X1) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19211 X0 X1 X2
       have i₂ := eq23 (σ (k X0 X0)) X1
       grind)
    | exact superpose eq23 eq19211
    | (have j0 := eq19211 X0 X1 X2
       grind)
    | exact resolve eq19211 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19211
  have eq19320 : ∀ X0 X1 X2 : G, (k (k X0 X0) X1) = (k (τ (M.op (σ X0) (σ X0))) X1) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19262 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq19262
    | (have j0 := eq19262 X0 X1 X2
       grind)
    | exact resolve eq19262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19262
  have eq22274 : ∀ X0 : G, (k (k X0 X0) X0) ≠ X0 ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19320 X0 x (τ (M.op (σ X0) (σ X0)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19320
  have eq22422 : ∀ X0 : G, (τ X0) ≠ (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (k (τ (M.op (σ (τ X0)) (σ (τ X0)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22274 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq22274
    | (have j0 := eq22274 (τ X0)
       grind)
    | exact resolve eq22274 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22274
  have eq22507 : ∀ X0 : G, (τ X0) ≠ (τ (k (k X0 X0) X0)) ∨ (τ X0) = (k (τ (M.op (σ (τ X0)) (σ (τ X0)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22422 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq22422
    | (have j0 := eq22422 X0
       grind)
    | exact resolve eq22422 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22422
  have eq22520 : ∀ X0 : G, (τ X0) = (τ (k (M.op (σ (τ X0)) (σ (τ X0))) X0)) ∨ (τ X0) ≠ (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq22507 X0
       have i₂ := eq32 X0 (M.op (σ (τ X0)) (σ (τ X0)))
       grind)
    | exact superpose eq32 eq22507
    | (have j0 := eq22507 X0
       grind)
    | exact resolve eq22507 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22507
  have eq22527 : ∀ X0 : G, (τ X0) ≠ (τ (k (k X0 X0) X0)) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq22520 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22520
    | (have j0 := eq22520 X0
       grind)
    | exact resolve eq22520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22520
  have eq43003 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq1417 X0
       grind)
    | exact superpose eq1417 eq62
    | exact resolve eq62 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43064 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43003 X0 X1
       have i₂ := eq1417 X0
       grind)
    | exact superpose eq1417 eq43003
    | exact resolve eq43003 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43003
  have eq43159 : ∀ X0 X1 : G, (M.op (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43064 (σ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq43064 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq43064 eq43064
    | exact resolve eq43064 eq43064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43064
  have eq43312 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43159 X0 X1
       have i₂ := eq1417 X0
       grind)
    | exact superpose eq1417 eq43159
    | exact resolve eq43159 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq43159
  have eq43398 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43312 (σ (σ (M.op (M.op X0 X0) X0))) X1
       have i₂ := eq43312 X0 (σ (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq43312 eq43312
    | exact resolve eq43312 eq43312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43312
  have eq43558 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43398 X0 X1
       have i₂ := eq1414 X0
       grind)
    | exact superpose eq1414 eq43398
    | exact resolve eq43398 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414 eq43398
  have eq89975 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq1422 X0
       grind)
    | exact superpose eq1422 eq62
    | exact resolve eq62 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90080 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89975 X0 X1
       have i₂ := eq1422 X0
       grind)
    | exact superpose eq1422 eq89975
    | exact resolve eq89975 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq89975
  have eq130991 : ∀ X0 : G, (σ X0) ≠ (σ (k (k X0 X0) X0)) ∨ (σ X0) = (k (M.op (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq181 X0 x (M.op (σ X0) (σ X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq147818 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq3771 x y X0
       grind)
    | exact superpose eq3771 eq16
    | (have j1 := eq3771 x y X0
       grind)
    | exact resolve eq16 eq3771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq159086 : ∀ X0 : G, (σ X0) ≠ (k (σ (M.op X0 X0)) (σ X0)) ∨ (k (σ (k X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3952 X0 x (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159099 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq159086 X0
       have j1 := eq3952 X0 x (σ X0)
       grind)
    | (have r₁ := eq159086 X0
       have r₂ := eq3952 X0 (σ (M.op X0 X0)) x
       grind)
    | exact resolve eq159086 eq3952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952 eq159086
  have eq159151 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq159099 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq159099
    | exact resolve eq159099 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159099
  have eq159176 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq159151 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq159151
    | exact resolve eq159151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159151
  have eq159254 : ∀ X0 : G, (σ (k (M.op (σ X0) (σ X0)) (σ X0))) = (σ (σ (k (k (τ (σ X0)) X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq159176 (σ X0)
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq159176
    | exact resolve eq159176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159345 : ∀ X0 : G, (σ X0) = (k (M.op (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) ≠ (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq130991 X0
       have i₂ := eq159176 X0
       grind)
    | exact superpose eq159176 eq130991
    | (have j0 := eq130991 X0
       grind)
    | exact resolve eq130991 eq159176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130991
  have eq159372 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq159176 X0
       grind)
    | exact superpose eq159176 eq10
    | exact resolve eq10 eq159176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159541 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq159372 X0
       have i₂ := eq10 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq159372
    | exact resolve eq159372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159372
  have eq159586 : ∀ X0 : G, (σ (k (M.op (σ X0) (σ X0)) (σ X0))) = (σ (σ (k (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq159254 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq159254
    | exact resolve eq159254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159254
  have eq159677 : ∀ X0 : G, (σ (k (M.op (σ X0) (σ X0)) (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq159586 X0
       have i₂ := eq159176 X0
       grind)
    | exact superpose eq159176 eq159586
    | exact resolve eq159586 eq159176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159586
  have eq159847 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq159541 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq159541
    | exact resolve eq159541 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159932 : ∀ X0 : G, (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (k (k X0 (τ (σ X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0 (σ X0) (σ X0)
       have i₂ := eq159541 (σ X0)
       grind)
    | exact superpose eq159541 eq42
    | exact resolve eq42 eq159541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq159935 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0 X0
       have i₂ := eq159541 (σ X0)
       grind)
    | exact superpose eq159541 eq22
    | exact resolve eq22 eq159541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq160118 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq159935 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq159935
    | exact resolve eq159935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159935
  have eq160120 : ∀ X0 : G, (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq159932 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq159932
    | exact resolve eq159932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159932
  have eq160138 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq159847 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq159847
    | exact resolve eq159847 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159847
  have eq160223 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq160118 X0
       have i₂ := eq159176 X0
       grind)
    | exact superpose eq159176 eq160118
    | exact resolve eq160118 eq159176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160118
  have eq160225 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq160120 X0
       have i₂ := eq159541 X0
       grind)
    | exact superpose eq159541 eq160120
    | exact resolve eq160120 eq159541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160120
  have eq160238 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq160138 X0
       have i₂ := eq159541 X0
       grind)
    | exact superpose eq159541 eq160138
    | exact resolve eq160138 eq159541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159541 eq160138
  have eq160268 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq160225 X0
       have i₂ := eq23 (M.op (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq23 eq160225
    | exact resolve eq160225 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160225
  have eq161220 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (M.op X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq161592 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq161220 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161220
    | (have j0 := eq161220 X0
       grind)
    | exact resolve eq161220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161220
  have eq161760 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq161592 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq161592
    | (have j0 := eq161592 X0
       grind)
    | exact resolve eq161592 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161592
  have eq222044 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) ≠ (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq159345 X0
       grind)
    | exact superpose eq159345 eq23
    | (have j1 := eq159345 X0
       grind)
    | exact resolve eq23 eq159345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159345
  have eq222069 : ∀ X0 : G, (τ (σ X0)) = (k (M.op X0 X0) X0) ∨ (σ X0) ≠ (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq222044 X0
       have i₂ := eq160268 X0
       grind)
    | exact superpose eq160268 eq222044
    | (have j0 := eq222044 X0
       grind)
    | exact resolve eq222044 eq160268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222044
  have eq222134 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op X0 X0) X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq222069 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq222069
    | (have j0 := eq222069 X0
       grind)
    | exact resolve eq222069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222069
  have eq222500 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (k (M.op X0 X0) X0))) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq222134 (τ X0)
       have i₂ := eq160238 X0
       grind)
    | exact superpose eq160238 eq222134
    | exact resolve eq222134 eq160238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222595 : ∀ X0 : G, (σ (τ X0)) ≠ (k (M.op X0 X0) X0) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq222500 X0
       have i₂ := eq11 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq222500
    | (have j0 := eq222500 X0
       grind)
    | exact resolve eq222500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222500
  have eq222623 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq222595 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq222595
    | (have j0 := eq222595 X0
       grind)
    | exact resolve eq222595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222595
  have eq222707 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq223043 : ∀ X0 : G, (τ X0) ≠ (τ (k (M.op X0 X0) X0)) ∨ (τ (τ X0)) = (τ (τ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq222623 (τ X0)
       have i₂ := eq160238 X0
       grind)
    | exact superpose eq160238 eq222623
    | exact resolve eq222623 eq160238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222623
  have eq223390 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq222707 X0
       have j1 := eq77 X0 x
       grind)
    | (have r₁ := eq222707 X0
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq222707 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222707
  have eq223954 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1464 X0
       have i₂ := eq223390 X0
       grind)
    | exact superpose eq223390 eq1464
    | (have j0 := eq1464 X0
       have j1 := eq223390 X0
       grind)
    | exact resolve eq1464 eq223390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq224013 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (k X0 X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (k X0 X0) X1
       have i₂ := eq223390 X0
       grind)
    | exact superpose eq223390 eq18
    | (have j1 := eq223390 X0
       grind)
    | exact resolve eq18 eq223390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224234 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq223954 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223954
  have eq224295 : ∀ X0 X1 : G, (k X0 (σ X1)) = (k (k X0 X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq224013 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq224013
    | (have j0 := eq224013 X0 X1
       grind)
    | exact resolve eq224013 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224013
  have eq230207 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq224234 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq224234
    | (have j0 := eq224234 (σ X0)
       grind)
    | exact resolve eq224234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230310 : ∀ X0 X1 : G, (M.op (M.op (τ (τ X0)) (τ (τ X0))) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ (τ X0)) X1
       have i₂ := eq224234 X0
       grind)
    | exact superpose eq224234 eq62
    | (have j1 := eq224234 X0
       grind)
    | exact resolve eq62 eq224234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224234
  have eq230478 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq230207 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq230207
    | (have j0 := eq230207 X0
       grind)
    | exact resolve eq230207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230207
  have eq236675 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (k (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22527 (σ X0)
       have i₂ := eq224295 (σ X0) X0
       grind)
    | exact superpose eq224295 eq22527
    | (have j0 := eq22527 (σ X0)
       have j1 := eq224295 (σ X0) x
       grind)
    | exact resolve eq22527 eq224295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22527 eq224295
  have eq236792 : ∀ X0 : G, (τ (σ X0)) = (τ (k (M.op (σ X0) (σ X0)) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq236675 X0
       have j1 := eq223390 (σ X0)
       grind)
    | (have r₁ := eq236675 X0
       have r₂ := eq223390 (σ X0)
       grind)
    | exact resolve eq236675 eq223390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223390 eq236675
  have eq236825 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq236792 X0
       have i₂ := eq23 (M.op (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq23 eq236792
    | (have j0 := eq236792 X0
       grind)
    | exact resolve eq236792 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236792
  have eq236850 : ∀ X0 : G, (τ (σ X0)) = (k (M.op X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq236825 X0
       have i₂ := eq160268 X0
       grind)
    | exact superpose eq160268 eq236825
    | (have j0 := eq236825 X0
       grind)
    | exact resolve eq236825 eq160268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160268 eq236825
  have eq236863 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq236850 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq236850
    | (have j0 := eq236850 X0
       grind)
    | exact resolve eq236850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236850
  have eq236871 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq236863 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq236863
    | (have j0 := eq236863 X0
       grind)
    | exact resolve eq236863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236863
  have eq237455 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq236871 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq236871
    | (have j0 := eq236871 (τ X0)
       grind)
    | exact resolve eq236871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237793 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq528 (σ X0)
       have i₂ := eq236871 X0
       grind)
    | exact superpose eq236871 eq528
    | (have j0 := eq528 X0
       have j1 := eq236871 X0
       grind)
    | exact resolve eq528 eq236871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq236871
  have eq237933 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ (k X0 X0))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq237793 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq237793
    | (have j0 := eq237793 X0
       grind)
    | exact resolve eq237793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237793
  have eq237982 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq237455 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq237455
    | (have j0 := eq237455 X0
       grind)
    | exact resolve eq237455 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq237455
  have eq238007 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ (k X0 X0))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq237933 X0
       have i₂ := eq159176 X0
       grind)
    | exact superpose eq159176 eq237933
    | (have j0 := eq237933 X0
       grind)
    | exact resolve eq237933 eq159176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237933
  have eq238030 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq237982 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq237982
    | (have j0 := eq237982 X0
       grind)
    | exact resolve eq237982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237982
  have eq238042 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ (k X0 X0))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq238007 X0
       have j1 := eq222134 X0
       grind)
    | (have r₁ := eq238007 X0
       have r₂ := eq222134 X0
       grind)
    | exact resolve eq238007 eq222134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222134 eq238007
  have eq238052 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq238030 X0
       have i₂ := eq160238 X0
       grind)
    | exact superpose eq160238 eq238030
    | (have j0 := eq238030 X0
       grind)
    | exact resolve eq238030 eq160238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238030
  have eq238962 : ∀ X0 : G, (σ (τ X0)) ≠ (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (τ X0) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq238042 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq238042
    | (have j0 := eq238042 (τ X0)
       grind)
    | exact resolve eq238042 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq238042
  have eq239114 : ∀ X0 : G, (M.op X0 (k X0 X0)) ≠ X0 ∨ (τ X0) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq238962 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq238962
    | (have j0 := eq238962 X0
       grind)
    | exact resolve eq238962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238962
  have eq239169 : ∀ X0 : G, (M.op X0 (k X0 X0)) ≠ X0 ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq239114 X0
       have i₂ := eq160238 X0
       grind)
    | exact superpose eq160238 eq239114
    | (have j0 := eq239114 X0
       grind)
    | exact resolve eq239114 eq160238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160238 eq239114
  have eq239272 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq239169 X0
       have i₂ := eq238052 X0
       grind)
    | exact superpose eq238052 eq239169
    | (have j0 := eq239169 X0
       have j1 := eq238052 X0
       grind)
    | exact resolve eq239169 eq238052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238052 eq239169
  have eq239642 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq239272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239272
  have eq244019 : ∀ X0 X1 : G, (σ (τ (τ X0))) = (k X1 (σ (τ (τ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ (τ X0)) X1
       have i₂ := eq230310 X0 (τ (τ X0))
       grind)
    | exact superpose eq230310 eq102
    | (have j1 := eq230310 X0 X1
       grind)
    | exact resolve eq102 eq230310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq244036 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (τ (τ X0)))))) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43558 (τ (τ X0)) X1
       have i₂ := eq230310 X0 (τ (τ X0))
       grind)
    | exact superpose eq230310 eq43558
    | (have j1 := eq230310 X0 X1
       grind)
    | exact resolve eq43558 eq230310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43558 eq230310
  have eq244260 : ∀ X0 X1 : G, (M.op (σ (σ (σ (τ X0)))) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq244036 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq244036
    | (have j0 := eq244036 X0 X1
       grind)
    | exact resolve eq244036 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244036
  have eq244269 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq244019 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq244019
    | (have j0 := eq244019 X0 X1
       grind)
    | exact resolve eq244019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244019
  have eq244282 : ∀ X0 X1 : G, (M.op (σ (σ X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq244260 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq244260
    | (have j0 := eq244260 X0 X1
       grind)
    | exact resolve eq244260 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244260
  have eq245470 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ X0)) = (k X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq244269 (σ X0) X1
       grind)
    | exact superpose eq244269 eq15
    | (have j1 := eq244269 (σ X0) X1
       grind)
    | exact resolve eq15 eq244269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244269
  have eq245558 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq245470 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq245470
    | (have j0 := eq245470 X0 X1
       grind)
    | exact resolve eq245470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245470
  have eq245788 : ∀ X0 : G, (k (σ (σ X0)) (σ (σ X0))) = (σ (k (M.op (σ X0) (σ X0)) (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq160223 (σ X0)
       have i₂ := eq244282 X0 (σ (σ X0))
       grind)
    | exact superpose eq244282 eq160223
    | (have j1 := eq244282 X0 x
       grind)
    | exact resolve eq160223 eq244282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160223
  have eq245808 : ∀ X0 X1 : G, (M.op (M.op (σ (σ X0)) (σ (σ X0))) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ (σ X0)) X1
       have i₂ := eq244282 X0 (σ (σ X0))
       grind)
    | exact superpose eq244282 eq62
    | (have j1 := eq244282 X0 X1
       grind)
    | exact resolve eq62 eq244282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245811 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (k (σ (σ X0)) (σ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq86 (σ (σ X0))
       have i₂ := eq244282 X0 (σ (σ X0))
       grind)
    | exact superpose eq244282 eq86
    | (have j0 := eq86 (σ (σ X0))
       have j1 := eq244282 X0 x
       grind)
    | (have r₁ := eq86 (σ (σ X0))
       have r₂ := eq244282 X0 (σ (σ X0))
       grind)
    | exact resolve eq86 eq244282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq244282
  have eq245974 : ∀ X0 : G, (σ (σ X0)) = (k (σ (σ X0)) (σ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq245811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245811
  have eq246009 : ∀ X0 : G, (σ (k (σ X0) (σ X0))) = (σ (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq245974 X0
       have i₂ := eq15 (σ X0) (σ X0)
       grind)
    | exact superpose eq15 eq245974
    | (have j0 := eq245974 X0
       grind)
    | exact resolve eq245974 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245974
  have eq246015 : ∀ X0 : G, (k (σ (σ X0)) (σ (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq245788 X0
       have i₂ := eq159677 X0
       grind)
    | exact superpose eq159677 eq245788
    | (have j0 := eq245788 X0
       grind)
    | exact resolve eq245788 eq159677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159677 eq245788
  have eq246044 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq246009 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq246009
    | (have j0 := eq246009 X0
       grind)
    | exact resolve eq246009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246009
  have eq246048 : ∀ X0 : G, (σ (k (σ X0) (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq246015 X0
       have i₂ := eq15 (σ X0) (σ X0)
       grind)
    | exact superpose eq15 eq246015
    | (have j0 := eq246015 X0
       grind)
    | exact resolve eq246015 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246015
  have eq246069 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq246048 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq246048
    | (have j0 := eq246048 X0
       grind)
    | exact resolve eq246048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246048
  have eq253360 : ∀ X0 : G, (σ (k X0 X0)) = (τ (σ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (σ (k X0 X0))
       have i₂ := eq246044 X0
       grind)
    | exact superpose eq246044 eq10
    | (have j1 := eq246044 X0
       grind)
    | exact resolve eq10 eq246044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246044
  have eq253632 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq253360 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq253360
    | (have j0 := eq253360 X0
       grind)
    | exact resolve eq253360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253360
  have eq253895 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (k X0 X0)
       have i₂ := eq253632 X0
       grind)
    | exact superpose eq253632 eq15
    | (have j1 := eq253632 X0
       grind)
    | exact resolve eq15 eq253632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253632
  have eq254100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq253895 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq253895
    | (have j0 := eq253895 X0 X1
       grind)
    | exact resolve eq253895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253895
  have eq260527 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (σ X0) (σ X0))) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq230478 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq230478
    | (have j0 := eq230478 (σ X0)
       grind)
    | exact resolve eq230478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230478
  have eq260777 : ∀ X0 : G, (σ (σ (k X0 X0))) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq260527 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq260527
    | (have j0 := eq260527 X0
       grind)
    | exact resolve eq260527 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260527
  have eq270004 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) X1) = X1 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq245808 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq245808
    | (have j0 := eq245808 (τ X0) X1
       grind)
    | exact resolve eq245808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245808
  have eq270446 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) X1) = X1 ∨ (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq270004 X0 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq270004
    | (have j0 := eq270004 X0 X1
       grind)
    | exact resolve eq270004 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq270004
  have eq278366 : ∀ X0 : G, (σ (σ (k X0 X0))) ≠ (σ (σ (k (k X0 X0) X0))) ∨ (σ (σ (k X0 X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1402 (k X0 X0)
       have i₂ := eq254100 X0 (k X0 X0)
       grind)
    | exact superpose eq254100 eq1402
    | (have j0 := eq1402 (k X0 X0)
       have j1 := eq254100 X0 x
       grind)
    | exact resolve eq1402 eq254100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq254100
  have eq278726 : ∀ X0 : G, (σ (σ (k X0 X0))) ≠ (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ (k X0 X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq278366 X0
       have i₂ := eq159176 X0
       grind)
    | exact superpose eq159176 eq278366
    | (have j0 := eq278366 X0
       grind)
    | exact resolve eq278366 eq159176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159176 eq278366
  have eq278819 : ∀ X0 : G, (σ (σ (k X0 X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278726 X0
       have j1 := eq246069 X0
       grind)
    | (have r₁ := eq278726 X0
       have r₂ := eq246069 X0
       grind)
    | exact resolve eq278726 eq246069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246069 eq278726
  have eq325451 : ∀ X0 X1 : G, (M.op (σ (σ (k X0 X0))) X1) = X1 ∨ (τ (k (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq270446 (σ X0) X1
       have i₂ := eq260777 X0
       grind)
    | exact superpose eq260777 eq270446
    | (have j0 := eq270446 (σ X0) X1
       have j1 := eq260777 X0
       grind)
    | exact resolve eq270446 eq260777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260777 eq270446
  have eq325812 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op (σ (σ (k X0 X0))) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq325451 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq325451
    | (have j0 := eq325451 X0 X1
       grind)
    | exact resolve eq325451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325451
  have eq325825 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op (σ (σ (k X0 X0))) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq325812 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq325812
    | (have j0 := eq325812 X0 X1
       grind)
    | exact resolve eq325812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325812
  have eq325831 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op (σ (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq325825 X0 X1
       have j1 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq325825 X0 (σ (σ (k X0 X0)))
       have r₂ := eq12 X0 (σ (σ (k X0 X0)))
       grind)
    | (have r₁ := eq325825 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq325825 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325825
  have eq325837 : ∀ X0 X1 : G, (M.op (σ (σ (k X0 X0))) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq325831 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq325831
    | (have j0 := eq325831 X0 X1
       grind)
    | exact resolve eq325831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325831
  have eq326189 : ∀ X0 : G, (σ (σ (k X0 X0))) ≠ (M.op (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))) ∨ (τ (σ (σ (k X0 X0)))) = (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq239642 (σ (σ (k X0 X0)))
       have i₂ := eq325837 X0 (σ (σ (k X0 X0)))
       grind)
    | exact superpose eq325837 eq239642
    | (have j1 := eq325837 X0 x
       grind)
    | exact resolve eq239642 eq325837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239642
  have eq326307 : ∀ X0 : G, (τ (σ (σ (k X0 X0)))) = (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq326189 X0
       have j1 := eq278819 X0
       grind)
    | (have r₁ := eq326189 X0
       have r₂ := eq278819 X0
       grind)
    | exact resolve eq326189 eq278819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278819 eq326189
  have eq326428 : ∀ X0 : G, (τ (σ (σ (k X0 X0)))) = (k (τ (σ (σ (k X0 X0)))) (σ (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq326307 X0
       have i₂ := eq23 (σ (σ (k X0 X0))) (σ (k X0 X0))
       grind)
    | exact superpose eq23 eq326307
    | (have j0 := eq326307 X0
       grind)
    | exact resolve eq326307 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326307
  have eq326505 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq326428 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq326428
    | (have j0 := eq326428 X0
       grind)
    | exact resolve eq326428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326428
  have eq326545 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq326505 X0
       have i₂ := eq15 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq15 eq326505
    | (have j0 := eq326505 X0
       grind)
    | exact resolve eq326505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326505
  have eq467731 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ x = X0 ∨ x = X0 ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq16570 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16570
  have eq467732 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ x = X0 ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq467731 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467731
  have eq467733 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq467732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467732
  have eq467847 : (k (σ (M.op x x)) x) = (M.op x (σ (k x x))) ∨ x = (σ (k x x)) := by
    first
    | (have i₁ := eq3969 x
       have i₂ := eq467733 (σ (k x x))
       grind)
    | exact superpose eq467733 eq3969
    | (have j1 := eq467733 (σ (k x x))
       grind)
    | exact resolve eq3969 eq467733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969
  have eq467924 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq147818 X0
       have i₂ := eq467733 y
       grind)
    | exact superpose eq467733 eq147818
    | (have j0 := eq147818 X0
       have j1 := eq467733 (k X0 x)
       grind)
    | exact resolve eq147818 eq467733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147818 eq467733
  have eq467927 : ∀ X0 : G, x = y ∨ x = (k X0 x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq467924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467924
  have eq469102 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (k X0 x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq467927 X0
       grind)
    | exact superpose eq467927 eq16
    | (have j1 := eq467927 X0
       grind)
    | exact resolve eq16 eq467927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467927
  have eq665649 : ∀ X0 : G, (τ (σ (σ (k X0 X0)))) ≠ (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0))))) ∨ (τ (τ (σ (σ (k X0 X0))))) = (τ (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq223043 (σ (σ (k X0 X0)))
       have i₂ := eq325837 X0 (σ (σ (k X0 X0)))
       grind)
    | exact superpose eq325837 eq223043
    | (have j1 := eq325837 X0 x
       grind)
    | exact resolve eq223043 eq325837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223043 eq325837
  have eq666204 : ∀ X0 : G, (τ (σ (σ (k X0 X0)))) ≠ (k (τ (σ (σ (k X0 X0)))) (σ (k X0 X0))) ∨ (τ (τ (σ (σ (k X0 X0))))) = (τ (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq665649 X0
       have i₂ := eq23 (σ (σ (k X0 X0))) (σ (k X0 X0))
       grind)
    | exact superpose eq23 eq665649
    | (have j0 := eq665649 X0
       grind)
    | exact resolve eq665649 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665649
  have eq666767 : ∀ X0 : G, (σ (k X0 X0)) ≠ (k (σ (k X0 X0)) (σ (k X0 X0))) ∨ (τ (τ (σ (σ (k X0 X0))))) = (τ (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq666204 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq666204
    | (have j0 := eq666204 X0
       grind)
    | exact resolve eq666204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666204
  have eq667183 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k (k X0 X0) (k X0 X0))) ∨ (τ (τ (σ (σ (k X0 X0))))) = (τ (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq666767 X0
       have i₂ := eq15 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq15 eq666767
    | (have j0 := eq666767 X0
       grind)
    | exact resolve eq666767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666767
  have eq667525 : ∀ X0 : G, (τ (τ (σ (σ (k X0 X0))))) = (τ (τ (k (σ (σ (k X0 X0))) (σ (σ (k X0 X0)))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq667183 X0
       have j1 := eq326545 X0
       grind)
    | (have r₁ := eq667183 X0
       have r₂ := eq326545 X0
       grind)
    | exact resolve eq667183 eq326545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326545 eq667183
  have eq667835 : ∀ X0 : G, (τ (τ (σ (σ (k X0 X0))))) = (τ (k (τ (σ (σ (k X0 X0)))) (σ (k X0 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq667525 X0
       have i₂ := eq23 (σ (σ (k X0 X0))) (σ (k X0 X0))
       grind)
    | exact superpose eq23 eq667525
    | (have j0 := eq667525 X0
       grind)
    | exact resolve eq667525 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667525
  have eq668103 : ∀ X0 : G, (τ (τ (σ (σ (k X0 X0))))) = (k (τ (τ (σ (σ (k X0 X0))))) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq667835 X0
       have i₂ := eq23 (τ (σ (σ (k X0 X0)))) (k X0 X0)
       grind)
    | exact superpose eq23 eq667835
    | (have j0 := eq667835 X0
       grind)
    | exact resolve eq667835 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq667835
  have eq668287 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq668103 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq668103
    | (have j0 := eq668103 X0
       grind)
    | exact resolve eq668103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668103
  have eq668437 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq668287 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq668287
    | (have j0 := eq668287 X0
       grind)
    | exact resolve eq668287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668287
  have eq668887 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1424 (k X0 X0)
       have i₂ := eq668437 X0
       grind)
    | exact superpose eq668437 eq1424
    | (have j0 := eq1424 (k X0 X0)
       have j1 := eq668437 X0
       grind)
    | (have r₁ := eq1424 (k X0 X0)
       have r₂ := eq668437 X0
       grind)
    | exact resolve eq1424 eq668437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq668437
  have eq669257 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq668887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668887
  have eq669553 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (k X0 X0) X1
       have i₂ := eq669257 X0
       grind)
    | exact superpose eq669257 eq62
    | (have j1 := eq669257 X0
       grind)
    | exact resolve eq62 eq669257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670944 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq90080 (k X0 X0) X1
       have i₂ := eq669553 X0 (k X0 X0)
       grind)
    | exact superpose eq669553 eq90080
    | (have j1 := eq669553 X0 X1
       grind)
    | exact resolve eq90080 eq669553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90080 eq669553
  have eq673720 : ∀ X0 X1 : G, (M.op (τ (σ (k X0 X0))) X1) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq670944 (σ X1) X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq670944
    | exact resolve eq670944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670944
  have eq674273 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq673720 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq673720
    | (have j0 := eq673720 X0 X1
       grind)
    | exact resolve eq673720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673720
  have eq677739 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674273 X0 X1
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq674273
    | (have j1 := eq77 X0 X2
       grind)
    | exact resolve eq674273 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq674273
  have eq993466 : ∀ X0 : G, (σ (k x x)) ≠ (σ (M.op x x)) ∨ x = (k X0 x) ∨ (σ x) = (σ y) ∨ (k x x) = (k (M.op x x) x) := by
    intro X0
    first
    | (have i₁ := eq469102 X0
       have i₂ := eq161760 x
       grind)
    | exact superpose eq161760 eq469102
    | (have j0 := eq469102 X0
       have j1 := eq161760 x
       grind)
    | exact resolve eq469102 eq161760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161760
  have eq993473 : ∀ X0 X1 : G, (σ (k x x)) ≠ (σ (M.op x x)) ∨ x = (k X0 x) ∨ (σ x) = (σ y) ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq469102 X0
       have i₂ := eq245558 x X1
       grind)
    | exact superpose eq245558 eq469102
    | (have j0 := eq469102 X0
       have j1 := eq245558 x X0
       grind)
    | exact resolve eq469102 eq245558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245558 eq469102
  have eq993576 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ x = (k X0 x) ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have j0 := eq993473 X0 X0
       have j1 := eq711 x X0
       grind)
    | (have r₁ := eq993473 X0 X1
       have r₂ := eq711 x X1
       grind)
    | exact resolve eq993473 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993473
  have eq993583 : ∀ X0 : G, (k x x) = (k (M.op x x) x) ∨ (σ x) = (σ y) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq993466 X0
       have j1 := eq711 x X0
       grind)
    | (have r₁ := eq993466 X0
       have r₂ := eq711 x x
       grind)
    | exact resolve eq993466 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq993466
  have eq998339 : x ≠ (k x x) ∨ (σ x) = (σ y) ∨ x = (k (M.op x x) x) := by
    first
    | (have j0 := eq993583 (M.op x x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993583
  have eq998340 : x = (k (M.op x x) x) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq993576 (M.op x x) (M.op x x)
       grind)
    | (have r₁ := eq998339
       have r₂ := eq993576 x x
       grind)
    | (have r₁ := eq998339
       have r₂ := eq993576 x x
       grind)
    | exact resolve eq998339 eq993576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993576 eq998339
  have eq998419 : ∀ X0 : G, x = (M.op x (M.op x x)) ∨ x = (k X0 x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq508 x X0
       have i₂ := eq998340
       grind)
    | exact superpose eq998340 eq508
    | (have j0 := eq508 x X0
       grind)
    | exact resolve eq508 eq998340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq998340
  have eq1000130 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ x = (k X1 x) ∨ (M.op (M.op x x) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq998419 X1
       grind)
    | exact superpose eq998419 eq9
    | (have j1 := eq998419 X1
       grind)
    | exact resolve eq9 eq998419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998419
  have eq1002757 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ x = (k X0 x) ∨ (M.op (M.op x x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq1000130 X1 X0
       grind)
    | exact superpose eq1000130 eq10
    | (have j1 := eq1000130 X1 X0
       grind)
    | exact resolve eq10 eq1000130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000130
  have eq1003190 : ∀ X0 X1 : G, x = y ∨ x = (k X0 x) ∨ (M.op (M.op x x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1002757 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1002757
    | (have j0 := eq1002757 X0 X1
       grind)
    | exact resolve eq1002757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002757
  have eq1003191 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (k X0 x) ∨ (M.op (M.op x x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1003190 X0 X1
       grind)
    | exact superpose eq1003190 eq16
    | (have j1 := eq1003190 X0 X1
       grind)
    | exact resolve eq16 eq1003190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003190
  have eq1003212 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = X1 ∨ x = (k X0 x) := by
    intro X0 X1
    first
    | (have j0 := eq1003191 X0 X1
       have j1 := eq677739 x X1 X0
       grind)
    | (have r₁ := eq1003191 X0 X1
       have r₂ := eq677739 x X1 x
       grind)
    | exact resolve eq1003191 eq677739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677739 eq1003191
  have eq1003255 : ∀ X0 X1 : G, x = (k X0 x) ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq72 x X1
       have i₂ := eq1003212 X0 x
       grind)
    | exact superpose eq1003212 eq72
    | (have j1 := eq1003212 X0 X1
       grind)
    | exact resolve eq72 eq1003212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1003212
  have eq1004919 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1003255 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003255
  have eq1004920 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1004919 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004919
  have eq1005535 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq669257 x
       have i₂ := eq1004920 x
       grind)
    | exact superpose eq1004920 eq669257
    | exact resolve eq669257 eq1004920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669257
  have eq1005806 : x = (M.op x x) := by grind
  clear eq1005535
  have eq1006013 : (k (σ x) x) = (M.op x (σ (k x x))) ∨ x = (σ (k x x)) := by
    first
    | (have i₁ := eq467847
       have i₂ := eq1005806
       grind)
    | exact superpose eq1005806 eq467847
    | exact resolve eq467847 eq1005806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467847
  have eq1006036 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 x X0
       have i₂ := eq1005806
       grind)
    | exact superpose eq1005806 eq62
    | exact resolve eq62 eq1005806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1006294 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1006036 X0
       have i₂ := eq1005806
       grind)
    | exact superpose eq1005806 eq1006036
    | exact resolve eq1006036 eq1005806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005806 eq1006036
  have eq1006296 : (k (σ x) x) = (M.op x (σ x)) ∨ x = (σ (k x x)) := by
    first
    | (have i₁ := eq1006013
       have i₂ := eq1004920 x
       grind)
    | exact superpose eq1004920 eq1006013
    | exact resolve eq1006013 eq1004920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006013
  have eq1006304 : (σ x) = (k (σ x) x) ∨ x = (σ (k x x)) := by
    first
    | (have i₁ := eq1006296
       have i₂ := eq1006294 (σ x)
       grind)
    | exact superpose eq1006294 eq1006296
    | exact resolve eq1006296 eq1006294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006296
  have eq1006306 : x = (σ x) ∨ x = (σ (k x x)) := by
    first
    | (have i₁ := eq1006304
       have i₂ := eq1004920 (σ x)
       grind)
    | exact superpose eq1004920 eq1006304
    | exact resolve eq1006304 eq1004920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006304
  have eq1006309 : x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1006306
       have i₂ := eq1004920 x
       grind)
    | exact superpose eq1004920 eq1006306
    | exact resolve eq1006306 eq1004920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004920 eq1006306
  have eq1006310 : x = (σ x) := by grind
  clear eq1006309
  have eq1007005 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1006310
       grind)
    | exact superpose eq1006310 eq16
    | exact resolve eq16 eq1006310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006310
  have eq1007504 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1007005
       have i₂ := eq1006294 (σ y)
       grind)
    | exact superpose eq1006294 eq1007005
    | exact resolve eq1007005 eq1006294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007005
  have eq1007568 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1007504
       have i₂ := eq1006294 y
       grind)
    | exact superpose eq1006294 eq1007504
    | exact resolve eq1007504 eq1006294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006294 eq1007504
  have eq1007569 : False := by grind
  exact eq1007569

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_x_pxy_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  clear eq36
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq562 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq183 eq184
    | exact resolve eq184 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq184
  have eq588 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X1) X0
       have i₂ := eq562 X1 X0
       grind)
    | exact superpose eq562 eq13
    | (have j0 := eq13 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq562 X0 X1
       grind)
    | exact resolve eq13 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) X0
       have i₂ := eq562 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq562 eq16
    | exact resolve eq16 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq588 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq653 : ∀ X0 X1 X2 : G, (M.op (M.op (k (M.op X0 X0) X1) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq590 X1 X0 X2
       have i₂ := eq593 X1 X0
       grind)
    | exact superpose eq593 eq590
    | exact resolve eq590 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq654 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq593 X1 X0
       grind)
    | exact superpose eq593 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 X0) ≠ (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq562 X0 X1
       grind)
    | exact superpose eq562 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq1017 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq562 X0 (M.op X0 X0)
       grind)
    | exact superpose eq562 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq562 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1017 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1030 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq593 X1 X0
       grind)
    | exact superpose eq593 eq1020
    | (have j0 := eq1020 X0 X1
       grind)
    | exact resolve eq1020 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1040 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1030 X0 X1
       have j1 := eq679 X0 X1
       grind)
    | (have r₁ := eq1030 X0 X1
       have r₂ := eq679 X0 X1
       grind)
    | (have r₁ := eq1030 X0 (M.op X0 X0)
       have r₂ := eq679 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1030 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq1030
  have eq1053 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1154 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 (M.op X1 X1)
       have i₂ := eq1040 X1 (σ X0)
       grind)
    | exact superpose eq1040 eq370
    | exact resolve eq370 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1155 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq1040 X1 (τ X0)
       grind)
    | exact superpose eq1040 eq34
    | exact resolve eq34 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1169 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1155 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1155
    | exact resolve eq1155 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1170 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1154
    | exact resolve eq1154 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1342 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (σ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq653 X0 (σ (M.op X1 X1)) X2
       have i₂ := eq1169 (M.op X0 X0) X1
       grind)
    | exact superpose eq1169 eq653
    | exact resolve eq653 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1373 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq1342 x X1 X2
       have i₂ := eq562 x (σ (M.op X1 X1))
       grind)
    | exact superpose eq562 eq1342
    | exact resolve eq1342 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1398 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (τ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq653 X0 (τ (M.op X1 X1)) X2
       have i₂ := eq1170 (M.op X0 X0) X1
       grind)
    | exact superpose eq1170 eq653
    | exact resolve eq653 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1417 : ∀ X1 X2 : G, (M.op (τ (M.op X1 X1)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq1398 x X1 X2
       have i₂ := eq562 x (τ (M.op X1 X1))
       grind)
    | exact superpose eq562 eq1398
    | exact resolve eq1398 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1432 : ∀ X0 : G, (M.op (σ (M.op (M.op y (M.op x y)) x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq1373
    | exact resolve eq1373 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1373
  have eq1497 : ∀ X0 : G, (M.op (τ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq1417
    | exact resolve eq1417 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1503 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (k (M.op X0 X0) X1) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1417 (M.op (k (M.op X0 X0) X1) X1) X2
       have i₂ := eq653 X0 X1 (M.op (k (M.op X0 X0) X1) X1)
       grind)
    | exact superpose eq653 eq1417
    | exact resolve eq1417 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq1417
  have eq2101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq40
    | exact resolve eq40 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1053
  have eq2102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2101
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2101
    | exact resolve eq2101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2102
    | exact resolve eq2102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq13734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2104 eq1054
    | exact resolve eq1054 eq2104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq2104
  have eq13746 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13734
       have r₂ := eq27
       grind)
    | exact resolve eq13734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13734
  have eq13761 : ∀ X0 : G, y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13746 eq1040
    | exact resolve eq1040 eq13746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq13746
  have eq14076 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 (σ y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1169 X0 y
       have i₂ := eq13761 X1
       grind)
    | exact superpose eq13761 eq1169
    | (have j1 := eq13761 X0
       grind)
    | exact resolve eq1169 eq13761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq13761
  have eq14182 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14076 X1 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14076
    | (have j0 := eq14076 X1 X1
       grind)
    | exact resolve eq14076 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14076
  have eq14945 : ∀ X0 : G, X0 ≠ X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14182 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14182
  have eq14946 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14945 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14945
  have eq14959 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14946 eq1104
    | (have j0 := eq1104 (σ y)
       grind)
    | (have r₁ := eq1104 (σ y)
       have r₂ := eq14946 (σ y)
       grind)
    | exact resolve eq1104 eq14946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq14974 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) (σ y))) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq14946 eq1503
    | exact resolve eq1503 eq14946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq14946
  have eq14996 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14959
  have eq15017 : ∀ X1 : G, (M.op (τ (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq14974 x X1
       have i₂ := eq562 x sF3
       grind)
    | exact superpose eq562 eq14974
    | exact resolve eq14974 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14974
  have eq15033 : ∀ X1 : G, (M.op y X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq31 eq15017
    | exact resolve eq15017 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15017
  have eq15045 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14996 eq593
    | exact resolve eq593 eq14996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq14996
  have eq16345 : ∀ X0 : G, X0 ≠ X0 ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq15033 X0
       grind)
    | exact superpose eq15033 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15033 x
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15033 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15033 x
       grind)
    | exact resolve eq13 eq15033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15033
  have eq16389 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16345
  have eq17309 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15045 eq26
    | (have j1 := eq15045 (σ x)
       grind)
    | exact resolve eq26 eq15045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15045
  have eq17561 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17309 eq114
    | exact resolve eq114 eq17309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq17309
  have eq18839 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16389 x
       grind)
    | exact superpose eq16389 eq18
    | (have j1 := eq16389 x
       grind)
    | exact resolve eq18 eq16389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16389
  have eq19128 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17561
       have i₂ := eq18839
       grind)
    | exact superpose eq18839 eq17561
    | exact resolve eq17561 eq18839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17561 eq18839
  have eq19134 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19128
  have eq19145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19134 eq14
    | exact resolve eq14 eq19134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19134
  have eq19147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq19145
    | exact resolve eq19145 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19145
  have eq19150 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19147
       have r₂ := eq27
       grind)
    | exact resolve eq19147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19147
  have eq19166 : ∀ X0 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19150 eq1497
    | exact resolve eq1497 eq19150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq19150
  have eq19196 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19166 X0
       have i₂ := eq562 sF3 sF2
       grind)
    | exact superpose eq562 eq19166
    | exact resolve eq19166 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19166
  have eq19217 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq19196
    | exact resolve eq19196 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19196
  have eq19729 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19217 y
       grind)
    | exact superpose eq19217 eq18
    | (have j1 := eq19217 y
       grind)
    | exact resolve eq18 eq19217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19217
  have eq19850 : y = (M.op x y) := by grind
  clear eq19729
  have eq19905 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19850
       grind)
    | exact superpose eq19850 eq24
    | exact resolve eq24 eq19850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq19926 : ∀ X0 : G, (M.op (σ (M.op (M.op (M.op x y) (M.op x y)) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1432 X0
       have i₂ := eq19850
       grind)
    | exact superpose eq19850 eq1432
    | exact resolve eq1432 eq19850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432 eq19850
  have eq19961 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19926 X0
       have i₂ := eq562 sF0 x
       grind)
    | exact superpose eq562 eq19926
    | exact resolve eq19926 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq19926
  have eq19981 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19961 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19961
    | (have j0 := eq19961 X0
       grind)
    | exact resolve eq19961 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19961
  have eq19988 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19905 eq20
    | exact resolve eq20 eq19905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19905
  have eq20418 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19981 eq26
    | (have j1 := eq19981 (σ y)
       grind)
    | exact resolve eq26 eq19981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19981
  have eq20596 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq20418 eq27
    | exact resolve eq27 eq20418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20418
  have eq20655 : False := by grind
  exact eq20655

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq40
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq19 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq173 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq139 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq139 eq9
    | exact resolve eq9 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq253 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq173 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq173
    | exact resolve eq173 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq173
  have eq289 : ∀ X0 X1 : G, (M.op (σ (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 (σ (M.op X0 X0)) X1
       have i₂ := eq253 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq253 eq253
    | exact resolve eq253 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq506 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq489 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq515 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq506 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq506 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq506 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq506 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq530 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq515 X0 X1
       have j1 := eq86 X0 (σ X1)
       grind)
    | (have r₁ := eq515 X0 X1
       have r₂ := eq86 X0 (σ X1)
       grind)
    | exact resolve eq515 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq515
  have eq541 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq530
    | (have j0 := eq530 X0 X1
       grind)
    | exact resolve eq530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq542 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq620 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq542 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq542
    | exact resolve eq542 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq632 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq542 x y
       grind)
    | exact superpose eq542 eq16
    | exact resolve eq16 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq253 X1 (σ X0)
       have i₂ := eq542 (M.op X1 X1) X0
       grind)
    | exact superpose eq542 eq253
    | exact resolve eq253 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq542
  have eq795 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X1 X1))
       have i₂ := eq635 X0 X1
       grind)
    | exact superpose eq635 eq10
    | exact resolve eq10 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq814 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq795
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq914 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq289 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq289 eq814
    | exact resolve eq814 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq814
  have eq1056 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 (σ (M.op X2 X2)) X1
       have i₂ := eq914 X2 X0
       grind)
    | exact superpose eq914 eq22
    | exact resolve eq22 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1065 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (k X0 (σ (σ (M.op X2 X2)))) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1056 X0 X1 X2
       have i₂ := eq620 X0 (σ (M.op X2 X2)) X1
       grind)
    | exact superpose eq620 eq1056
    | exact resolve eq1056 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq1056
  have eq1073 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1 x
       have i₂ := eq914 x X0
       grind)
    | exact superpose eq914 eq1065
    | exact resolve eq1065 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq1065
  have eq1191 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1073
    | exact resolve eq1073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1397 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq632
       have i₂ := eq1191 y x
       grind)
    | exact superpose eq1191 eq632
    | exact resolve eq632 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq1191
  have eq1398 : False := by grind
  exact eq1398

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq71
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq71
  have eq93 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq9
    | exact resolve eq9 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) (σ (M.op (M.op X0 (M.op X1 X0)) X1))) (σ (M.op (M.op X0 (M.op X1 X0)) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq134 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1))) (σ (M.op (M.op X0 (M.op X1 X0)) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X0 X1 X2
       have i₂ := eq82 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | exact superpose eq82 eq118
    | exact resolve eq118 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq139 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) (σ (M.op (M.op X0 (M.op X1 X0)) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X0 X1 X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq134
    | exact resolve eq134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq141 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 X1 X2
       have i₂ := eq82 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | exact superpose eq82 eq139
    | exact resolve eq139 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 X0 X1 X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq141
    | exact resolve eq141 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq539 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq61 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq609 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq539 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq539 eq9
    | exact resolve eq9 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq2101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2101 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2101
    | (have j0 := eq2101 (σ X0) (σ X1)
       grind)
    | exact resolve eq2101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3589 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2102 X1 X0
       have i₂ := eq2101 X1 X0
       grind)
    | exact superpose eq2101 eq2102
    | (have j0 := eq2102 X1 X0
       have j1 := eq2101 (σ X1) (σ X0)
       grind)
    | exact resolve eq2102 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq21148 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3589 x y
       grind)
    | exact superpose eq3589 eq16
    | (have j1 := eq3589 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3589 x y
       grind)
    | exact resolve eq16 eq3589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq21290 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21148
  have eq21349 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21290
       grind)
    | exact superpose eq21290 eq16
    | exact resolve eq16 eq21290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21351 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq21290
       grind)
    | exact superpose eq21290 eq12
    | exact resolve eq12 eq21290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21352 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq21290
       grind)
    | exact superpose eq21290 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21290
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21290
       grind)
    | exact resolve eq13 eq21290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21290
  have eq21371 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21352
  have eq21391 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21371
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq21371
    | exact resolve eq21371 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21371
  have eq21392 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21351
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq21351
    | exact resolve eq21351 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq21351
  have eq21400 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21391
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21391
    | exact resolve eq21391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21391
  have eq21401 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21392
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21392
    | exact resolve eq21392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21392
  have eq21402 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2101 eq21400
    | (have j1 := eq2101 y x
       grind)
    | exact resolve eq21400 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21400
  have eq21403 : (σ (M.op x y)) = (σ y) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2101 eq21401
    | (have j1 := eq2101 y x
       grind)
    | exact resolve eq21401 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101 eq21401
  have eq21405 : y = (M.op x y) := by grind
  clear eq21349 eq21402 eq21403
  have eq21407 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21405
       grind)
    | exact superpose eq21405 eq16
    | exact resolve eq16 eq21405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21412 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq143 y x X0
       have i₂ := eq21405
       grind)
    | exact superpose eq21405 eq143
    | exact resolve eq143 eq21405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq21405
  have eq21446 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21412 X0
       have i₂ := eq609 y x
       grind)
    | (have i₁ := eq21412 X0
       have i₂ := eq609 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq609 eq21412
    | exact resolve eq21412 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq21412
  have eq22112 : False := by grind
  exact eq22112

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X1 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq48
    | (have j0 := eq48 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq19
    | exact resolve eq19 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq87 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq87
    | exact resolve eq87 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq87
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 y x
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq163
       have i₂ := eq48 y x
       grind)
    | exact superpose eq48 eq163
    | (have j1 := eq48 (σ x) (σ y)
       grind)
    | (have r₁ := eq163
       have r₂ := eq48 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq163
       have r₂ := eq48 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq163 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq163
  have eq266 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq265
  have eq267 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq266
       grind)
    | exact superpose eq266 eq16
    | exact resolve eq16 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq268 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq267
       have r₂ := eq99 x
       grind)
    | exact resolve eq267 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq304 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq268
       grind)
    | exact superpose eq268 eq10
    | exact resolve eq10 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq319 : x = y := by
    first
    | (have i₁ := eq304
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq304
    | exact resolve eq304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq321 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq319
       grind)
    | exact superpose eq319 eq16
    | exact resolve eq16 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq322 : False := by grind
  exact eq322

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq14 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ X0) (σ X1)
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 (τ X0) X1 X2
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 (M.op (M.op X1 X1) X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq24 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq24 eq86
    | exact resolve eq86 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq152 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op X0 X0) x x X3
       have i₂ := eq24 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq180 : ∀ X0 X1 X2 X3 X4 : G, (k X3 (σ (M.op X4 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X4)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq110 X4 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3
       have i₂ := eq25 X0 X1 X2 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0)
       grind)
    | exact superpose eq25 eq110
    | exact resolve eq110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq194 : ∀ X3 X4 : G, (k X3 (σ (M.op X4 X4))) = X3 := by
    intro X3 X4
    first
    | (have i₁ := eq180 x x x X3 X4
       have i₂ := eq25 x x x X4
       grind)
    | exact superpose eq25 eq180
    | exact resolve eq180 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq180
  have eq204 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq226 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ (M.op X1 X1))
       have i₂ := eq194 (σ X0) X1
       grind)
    | exact superpose eq194 eq31
    | exact resolve eq31 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq231 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq226
    | exact resolve eq226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq232 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq231
    | exact resolve eq231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq238 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X1)
       have i₂ := eq232 (σ X0) X1
       grind)
    | exact superpose eq232 eq31
    | exact resolve eq31 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq242 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq238
    | exact resolve eq238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq681 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq204
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq204
    | (have j1 := eq44 (σ y) (σ x)
       grind)
    | exact resolve eq204 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq204
  have eq682 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq681
  have eq1160 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq152 y X0
       have i₂ := eq682
       grind)
    | exact superpose eq682 eq152
    | exact resolve eq152 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1802 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 (σ y)
       have i₂ := eq1160 X1
       grind)
    | exact superpose eq1160 eq242
    | (have j1 := eq1160 X1
       grind)
    | exact resolve eq242 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1160
  have eq1832 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1802 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1802
    | (have j0 := eq1802 X0 X1
       grind)
    | exact resolve eq1802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1860 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq215
    | (have j0 := eq215 (τ X0)
       grind)
    | exact resolve eq215 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1891 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1860 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1860
    | (have j0 := eq1860 X0
       grind)
    | exact resolve eq1860 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq1907 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1891 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1891
    | (have j0 := eq1891 X0
       grind)
    | exact resolve eq1891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq1963 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1907 x
       have i₂ := eq1832 x X0
       grind)
    | exact superpose eq1832 eq1907
    | (have j0 := eq1907 x
       have j1 := eq1832 X0 x
       grind)
    | (have r₁ := eq1907 x
       have r₂ := eq1832 x x
       grind)
    | exact resolve eq1907 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832 eq1907
  have eq1976 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1963 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq2018 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq1976 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq2019 : x = (M.op x x) := by grind
  clear eq2018
  have eq2035 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq152 x X0
       have i₂ := eq2019
       grind)
    | exact superpose eq2019 eq152
    | exact resolve eq152 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2038 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq232 X0 x
       have i₂ := eq2019
       grind)
    | exact superpose eq2019 eq232
    | exact resolve eq232 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq2019
  have eq2152 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq215 x
       have i₂ := eq2038 x
       grind)
    | exact superpose eq2038 eq215
    | (have j0 := eq215 x
       grind)
    | exact resolve eq215 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq2038
  have eq2163 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2152
  have eq4470 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq152 (σ x) X0
       have i₂ := eq2163
       grind)
    | exact superpose eq2163 eq152
    | exact resolve eq152 eq2163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2163
  have eq4657 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4470 (σ y)
       grind)
    | exact superpose eq4470 eq16
    | exact resolve eq16 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq4781 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4657
       have i₂ := eq2035 y
       grind)
    | exact superpose eq2035 eq4657
    | exact resolve eq4657 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq4657
  have eq4782 : False := by grind
  exact eq4782
