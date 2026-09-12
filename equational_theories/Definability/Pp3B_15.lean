import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq54 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op X1 X0) (M.op X1 X1) X2
       have i₂ := eq9 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq318 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X2 (M.op X1 X0))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 (M.op X0 X0) (M.op X1 (M.op X0 X2)) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0) X2
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq75
    | exact resolve eq75 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op X3 X1) (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X2 X3
       have i₂ := eq75 X1 X2 X0
       grind)
    | (have i₁ := eq62 X0 X0 X2
       have i₂ := eq75 X0 X0 X0
       grind)
    | exact superpose eq75 eq62
    | exact resolve eq62 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X2 X1)
       have i₂ := eq75 X1 X2 X0
       grind)
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq75 X0 X0 X0
       grind)
    | exact superpose eq75 eq54
    | exact resolve eq54 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq318 X1 X2 (M.op X2 X1) (M.op x X1)
       have i₂ := eq62 X1 X2 x
       grind)
    | exact superpose eq62 eq318
    | exact resolve eq318 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X2 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 (M.op X1 X1) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq382
    | exact resolve eq382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq382
    | exact resolve eq382 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 (M.op (M.op X2 X1) (M.op X2 X1)) (M.op X0 X1)
       have i₂ := eq62 X1 X2 X0
       grind)
    | exact superpose eq62 eq382
    | exact resolve eq382 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq431 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = (M.op (M.op X1 X0) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq408 X0 X1 X2
       have i₂ := eq409 (M.op X1 X0) X2
       grind)
    | exact superpose eq409 eq408
    | exact resolve eq408 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq475 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq475 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq571 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 X1 X2
       have i₂ := eq409 X0 X1
       grind)
    | exact superpose eq409 eq75
    | exact resolve eq75 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq594 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X1 X0) X2
       have i₂ := eq409 X0 X1
       grind)
    | exact superpose eq409 eq56
    | exact resolve eq56 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq571 X1 (M.op X0 X0) X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq571
    | exact resolve eq571 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq571 X0 (M.op X1 X0) X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq571
    | exact resolve eq571 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq736 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq666 X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | (have i₁ := eq666 X0 X1 X2
       have i₂ := eq54 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq54 eq666
    | exact resolve eq666 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq779 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X1)) (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq318 (M.op X1 X1) (M.op X0 (M.op X2 X1)) X4 X3
       have i₂ := eq736 X1 X2 X0
       grind)
    | exact superpose eq736 eq318
    | exact resolve eq318 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) (M.op X0 (M.op X2 X1))) = (M.op X1 (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 (M.op X1 X1) (M.op X0 (M.op X2 X1))
       have i₂ := eq736 X1 X2 X0
       grind)
    | exact superpose eq736 eq382
    | exact resolve eq382 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq787 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 X1))) = (M.op (M.op X2 X1) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq780 X0 X1 X2
       have i₂ := eq409 (M.op X2 X1) X0
       grind)
    | exact superpose eq409 eq780
    | exact resolve eq780 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq788 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq779 X0 X1 X2 X3 X4
       have i₂ := eq409 (M.op X2 X1) X0
       grind)
    | exact superpose eq409 eq779
    | exact resolve eq779 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq792 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq788 X0 X1 X2 X3 X4
       have i₂ := eq787 X0 X1 X2
       grind)
    | exact superpose eq787 eq788
    | exact resolve eq788 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq788
  have eq1385 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X1 X3)) (M.op X2 X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq338 x (M.op (M.op x X2) (M.op X2 X1)) (M.op X3 X1)
       have i₂ := eq326 x X1 X2 X3
       grind)
    | exact superpose eq326 eq338
    | exact resolve eq338 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq338
  have eq1400 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X4 (M.op X1 X3)) (M.op X2 X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1385 X1 X2 X3 X4
       have i₂ := eq431 X3 X2 (M.op X4 (M.op X1 X3))
       grind)
    | exact superpose eq431 eq1385
    | exact resolve eq1385 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1763 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq481 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1764 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1763 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1766 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1764 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1764
    | (have j0 := eq1764 (σ X0) (σ X1)
       grind)
    | exact resolve eq1764 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1764 (τ X0) X1
       grind)
    | exact superpose eq1764 eq17
    | (have j1 := eq1764 (τ X0) X1
       grind)
    | exact resolve eq17 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1764
  have eq1948 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq411 X1 X0 X2
       have i₂ := eq409 X0 X1
       grind)
    | exact superpose eq409 eq411
    | exact resolve eq411 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq411
  have eq2114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X1) = (M.op (M.op X4 (M.op X2 X1)) (M.op (M.op (M.op X0 (M.op X3 X1)) (M.op X2 X1)) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq594 (M.op (M.op X4 (M.op X1 X3)) (M.op X2 X3)) X2 X2
       have i₂ := eq1400 X1 X2 X3 X4
       grind)
    | exact superpose eq1400 eq594
    | exact resolve eq594 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq1400
  have eq2121 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X1)) (M.op X2 X1)) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2114 X0 X1 X2 X3 x
       have i₂ := eq792 (M.op (M.op X0 (M.op X3 X1)) (M.op X2 X1)) X1 X2 x X2
       grind)
    | exact superpose eq792 eq2114
    | exact resolve eq2114 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq2114
  have eq2137 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X2 X1) (M.op X2 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq2121 x X1 X2 x
       have i₂ := eq321 X2 X1 X2 (M.op x (M.op x X1))
       grind)
    | exact superpose eq321 eq2121
    | exact resolve eq2121 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq2121
  have eq2149 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq2137 X1 X2
       have i₂ := eq1948 X1 X2 X2
       grind)
    | exact superpose eq1948 eq2137
    | exact resolve eq2137 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq2137
  have eq2181 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2149 X1 X2
       have i₂ := eq571 X1 X2 X0
       grind)
    | (have i₁ := eq2149 (M.op X2 X1) X1
       have i₂ := eq571 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq571 eq2149
    | exact resolve eq2149 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq4248 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1785 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1785
    | exact resolve eq1785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq4293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4248 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4248
    | (have j0 := eq4248 X0 X1
       grind)
    | exact resolve eq4248 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq5433 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 X0) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq571 (M.op X2 X1) X0 X3
       have i₂ := eq431 X1 X2 X0
       grind)
    | exact superpose eq431 eq571
    | exact resolve eq571 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq571
  have eq8167 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X3 X2) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5433 X1 (M.op X2 X1) (M.op X0 X2) X3
       have i₂ := eq2181 X0 X1 X2
       grind)
    | exact superpose eq2181 eq5433
    | exact resolve eq5433 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq5433
  have eq21401 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1766 x y
       grind)
    | exact superpose eq1766 eq16
    | (have j1 := eq1766 x y
       grind)
    | exact resolve eq16 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21503 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1766 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq21519 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X1 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21503 (τ X1) (τ X0)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq21503
    | (have j0 := eq21503 (τ X1) (τ X0)
       grind)
    | exact resolve eq21503 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21503
  have eq21527 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21519 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq21519
    | (have j0 := eq21519 X0 X1
       grind)
    | exact resolve eq21519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21519
  have eq21529 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21527 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21527
    | (have j0 := eq21527 X0 X1
       grind)
    | exact resolve eq21527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21527
  have eq21530 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21529 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21529
    | (have j0 := eq21529 X0 X1
       grind)
    | exact resolve eq21529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21529
  have eq21531 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21530 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq21530
    | (have j0 := eq21530 X0 X1
       grind)
    | exact resolve eq21530 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21530
  have eq21634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21401
       have i₂ := eq4293 x y
       grind)
    | exact superpose eq4293 eq21401
    | (have j1 := eq4293 (σ x) (σ y)
       grind)
    | (have r₁ := eq21401
       have r₂ := eq4293 x y
       grind)
    | exact resolve eq21401 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq21635 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21634
  have eq21648 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq382 (σ y) (σ x)
       have i₂ := eq21635
       grind)
    | exact superpose eq21635 eq382
    | exact resolve eq382 eq21635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22332 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op X1 (σ x)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8167 (σ y) X1 (σ x) x
       have i₂ := eq21648
       grind)
    | exact superpose eq21648 eq8167
    | exact resolve eq8167 eq21648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8167 eq21648
  have eq22343 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22332 X0 x
       have i₂ := eq56 (σ x) x
       grind)
    | exact superpose eq56 eq22332
    | exact resolve eq22332 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq22332
  have eq36868 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22343 (σ x)
       have i₂ := eq21635
       grind)
    | exact superpose eq21635 eq22343
    | exact resolve eq22343 eq21635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22343
  have eq37000 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq36868
  have eq37094 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq382 (M.op (σ x) (σ x)) (σ y)
       have i₂ := eq37000
       grind)
    | exact superpose eq37000 eq382
    | exact resolve eq382 eq37000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37000
  have eq37362 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54 (σ y)
       have i₂ := eq37094
       grind)
    | exact superpose eq37094 eq54
    | exact resolve eq54 eq37094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37094
  have eq37485 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37362
       have i₂ := eq21635
       grind)
    | exact superpose eq21635 eq37362
    | exact resolve eq37362 eq21635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37362
  have eq37582 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37485
  have eq37635 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) x
       have i₂ := eq37582
       grind)
    | exact superpose eq37582 eq73
    | (have r₁ := eq73 (σ y) x
       have r₂ := eq37582
       grind)
    | exact resolve eq73 eq37582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37582
  have eq37713 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq37635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37635
  have eq37741 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37713 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq37713
    | exact resolve eq37713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37713
  have eq38021 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21635
       have i₂ := eq37741 x
       grind)
    | exact superpose eq37741 eq21635
    | exact resolve eq21635 eq37741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21635 eq37741
  have eq38146 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq38021
  have eq38462 : (k x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq38146
       grind)
    | exact superpose eq38146 eq10
    | exact resolve eq10 eq38146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38146
  have eq38528 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38462
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38462
    | exact resolve eq38462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38462
  have eq38550 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21531 y x
       have i₂ := eq38528
       grind)
    | exact superpose eq38528 eq21531
    | (have j0 := eq21531 y x
       grind)
    | (have r₁ := eq21531 y x
       have r₂ := eq38528
       grind)
    | exact resolve eq21531 eq38528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21531 eq38528
  have eq38565 : y ≠ y ∨ y = (M.op x y) := by grind
  clear eq38550
  have eq38566 : y = (M.op x y) := by grind
  clear eq38565
  have eq38592 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq318 y x X1 X0
       have i₂ := eq38566
       grind)
    | exact superpose eq38566 eq318
    | exact resolve eq318 eq38566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq39116 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq38592 X0 x
       have i₂ := eq38566
       grind)
    | exact superpose eq38566 eq38592
    | exact resolve eq38592 eq38566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38592
  have eq39314 : (M.op y (M.op x x)) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq657 y x
       have i₂ := eq39116 y
       grind)
    | exact superpose eq39116 eq657
    | exact resolve eq657 eq39116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq39116
  have eq39437 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq39314
       have i₂ := eq54 x
       grind)
    | (have i₁ := eq39314
       have i₂ := eq54 (M.op x (M.op x x))
       grind)
    | exact superpose eq54 eq39314
    | exact resolve eq39314 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq39314
  have eq39485 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq382 (M.op x x) y
       have i₂ := eq39437
       grind)
    | exact superpose eq39437 eq382
    | exact resolve eq382 eq39437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq39437
  have eq39593 : y = (M.op y y) := by
    first
    | (have i₁ := eq39485
       have i₂ := eq38566
       grind)
    | exact superpose eq38566 eq39485
    | exact resolve eq39485 eq38566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39485
  have eq39851 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq73 y x
       have i₂ := eq39593
       grind)
    | exact superpose eq39593 eq73
    | (have r₁ := eq73 y x
       have r₂ := eq39593
       grind)
    | exact resolve eq73 eq39593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq39593
  have eq39922 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq39851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39851
  have eq40052 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21401
       have i₂ := eq39922 x
       grind)
    | exact superpose eq39922 eq21401
    | exact resolve eq21401 eq39922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21401 eq39922
  have eq40055 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40052
  have eq40099 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40055
       grind)
    | exact superpose eq40055 eq16
    | exact resolve eq16 eq40055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40055
  have eq40199 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq40099
       have i₂ := eq38566
       grind)
    | exact superpose eq38566 eq40099
    | exact resolve eq40099 eq38566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38566 eq40099
  have eq40200 : False := by grind
  exact eq40200

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
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
  have eq62 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq64 X0 X2
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq390 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq390
    | exact resolve eq390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq530 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq538 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq502 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq502
    | exact resolve eq502 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq570 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq530
    | (have j0 := eq530 (σ X0) (σ X1)
       grind)
    | exact resolve eq530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq530
    | (have j0 := eq530 (τ X0) (τ X1)
       grind)
    | exact resolve eq530 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq585 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq530 (σ X0) X1
       grind)
    | exact superpose eq530 eq28
    | (have j1 := eq530 (σ X0) X1
       grind)
    | exact resolve eq28 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq530 (τ X0) X1
       grind)
    | exact superpose eq530 eq17
    | (have j1 := eq530 (τ X0) X1
       grind)
    | exact resolve eq17 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq748 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq538 X0 X2
       grind)
    | exact superpose eq538 eq70
    | exact resolve eq70 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq867 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq502 (M.op X2 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq748 X1 X2 X0
       grind)
    | exact superpose eq748 eq502
    | exact resolve eq502 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq869 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq867 X0 X1 X2
       have i₂ := eq538 X1 X2
       grind)
    | exact superpose eq538 eq867
    | exact resolve eq867 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq867
  have eq897 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq869 X0 X1 X0
       grind)
    | exact superpose eq869 eq87
    | exact resolve eq87 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq869
  have eq2833 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq530 X0 X1
       grind)
    | exact superpose eq530 eq570
    | (have j0 := eq570 X0 X1
       have j1 := eq530 (σ X0) (σ X1)
       grind)
    | exact resolve eq570 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq4775 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq590 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq62 (τ X0)
       grind)
    | exact superpose eq62 eq590
    | (have j0 := eq590 X0 (τ X0)
       grind)
    | exact resolve eq590 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4791 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4775 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4775
    | (have j0 := eq4775 X0
       grind)
    | exact resolve eq4775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq4793 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq590 eq4791
    | (have j0 := eq4791 X0
       have j1 := eq590 X0 (τ X0)
       grind)
    | exact resolve eq4791 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4791
  have eq4794 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4793 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4793
    | (have j0 := eq4793 X0
       grind)
    | exact resolve eq4793 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4793
  have eq4838 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq4794 X0
       grind)
    | exact superpose eq4794 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq4794 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq4794 X0
       grind)
    | exact resolve eq12 eq4794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4794
  have eq4847 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4838
  have eq5070 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq585 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq585
    | (have j0 := eq585 X0 (σ X0)
       grind)
    | exact resolve eq585 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5104 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5070 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5070
    | (have j0 := eq5070 X0
       grind)
    | exact resolve eq5070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5070
  have eq5108 : ∀ X0 : G, (k X0 (k X0 (τ (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq585 eq5104
    | (have j0 := eq5104 X0
       have j1 := eq585 X0 (σ X0)
       grind)
    | exact resolve eq5104 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq5104
  have eq5109 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5108 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5108
    | (have j0 := eq5108 X0
       grind)
    | exact resolve eq5108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5108
  have eq5162 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) X1
       have i₂ := eq5109 X0
       grind)
    | exact superpose eq5109 eq85
    | (have j1 := eq5109 X0
       grind)
    | (have r₁ := eq85 (σ X0) X1
       have r₂ := eq5109 X0
       grind)
    | exact resolve eq85 eq5109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5109
  have eq5169 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq5198 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4847 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4847
    | (have j0 := eq4847 (σ X0) X1
       grind)
    | exact resolve eq4847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq5232 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5198 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5198
    | (have j0 := eq5198 X0 X1
       grind)
    | exact resolve eq5198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198
  have eq5234 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5232 X0 X1
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq5232
    | (have j0 := eq5232 X0 X1
       grind)
    | exact resolve eq5232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5232
  have eq5245 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5169 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5169
    | (have j0 := eq5169 X1 X1
       grind)
    | exact resolve eq5169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169
  have eq5261 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5234 X0 X1
       have i₂ := eq530 X0 X0
       grind)
    | exact superpose eq530 eq5234
    | (have j0 := eq5234 X0 X1
       have j1 := eq530 X1 X0
       grind)
    | exact resolve eq5234 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5281 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq5234 X0 X1
       grind)
    | exact superpose eq5234 eq10
    | (have j1 := eq5234 X0 X1
       grind)
    | exact resolve eq10 eq5234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234
  have eq5296 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5281 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5281
    | (have j0 := eq5281 X0 X1
       grind)
    | exact resolve eq5281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5281
  have eq5311 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5261 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq5261 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq5261 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261
  have eq5412 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq5311 X0 X1
       grind)
    | exact superpose eq5311 eq10
    | (have j1 := eq5311 X0 X1
       grind)
    | exact resolve eq10 eq5311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311
  have eq5425 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5412 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5412
    | (have j0 := eq5412 X0 X1
       grind)
    | exact resolve eq5412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5412
  have eq5464 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq5425 X1 (σ X0)
       grind)
    | exact superpose eq5425 eq28
    | (have j1 := eq5425 X1 X1
       grind)
    | exact resolve eq28 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq5296 eq5245
    | (have j0 := eq5245 X0 X1
       have j1 := eq5296 X1 X1
       grind)
    | exact resolve eq5245 eq5296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245 eq5296
  have eq18178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14280 x y
       grind)
    | exact superpose eq14280 eq16
    | (have j1 := eq14280 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq14280 x y
       grind)
    | exact resolve eq16 eq14280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14280
  have eq18282 : y = (k y (k y y)) := by grind
  clear eq18178
  have eq18325 : y = (k y (M.op y y)) ∨ y = (k y (M.op y y)) := by
    first
    | (have i₁ := eq18282
       have i₂ := eq5425 y y
       grind)
    | exact superpose eq5425 eq18282
    | (have j1 := eq5425 y x
       grind)
    | exact resolve eq18282 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5425 eq18282
  have eq18335 : y = (k y (M.op y y)) := by grind
  clear eq18325
  have eq23359 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2833 x y
       grind)
    | exact superpose eq2833 eq16
    | (have j1 := eq2833 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2833 x y
       grind)
    | exact resolve eq16 eq2833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833
  have eq23474 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23359
  have eq23571 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq502 (σ x) (σ y)
       have i₂ := eq23474
       grind)
    | exact superpose eq23474 eq502
    | exact resolve eq502 eq23474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23697 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq897 (σ y) (σ x) x
       have i₂ := eq23571
       grind)
    | exact superpose eq23571 eq897
    | exact resolve eq897 eq23571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23571
  have eq23763 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23697 X0
       have i₂ := eq62 (σ x)
       grind)
    | exact superpose eq62 eq23697
    | exact resolve eq23697 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23697
  have eq32670 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5464 x (σ y)
       have i₂ := eq23474
       grind)
    | exact superpose eq23474 eq5464
    | (have j0 := eq5464 x (σ y)
       grind)
    | exact resolve eq5464 eq23474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5464
  have eq32717 : y = (k x y) ∨ (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32670
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq32670
    | exact resolve eq32670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32670
  have eq32755 : y = (M.op x y) ∨ (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq530 eq32717
    | (have j1 := eq530 x y
       grind)
    | exact resolve eq32717 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq32717
  have eq32756 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq32755
  have eq32806 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y (M.op (σ y) (σ y))
       have i₂ := eq32756
       grind)
    | exact superpose eq32756 eq28
    | exact resolve eq28 eq32756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32756
  have eq32811 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32806
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq32806
    | exact resolve eq32806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32806
  have eq56373 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq571 X0 X0
       grind)
    | exact superpose eq571 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq571 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq571 X1 X1
       grind)
    | exact resolve eq12 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq56519 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq56373 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq56373 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq56373 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56373
  have eq56850 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56519 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq56519
    | (have j0 := eq56519 (σ X0) X1
       grind)
    | exact resolve eq56519 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq56519
  have eq56851 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56850 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56850
    | (have j0 := eq56850 X0 X1
       grind)
    | exact resolve eq56850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56850
  have eq56860 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56851 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56851
    | (have j0 := eq56851 X0 X1
       grind)
    | exact resolve eq56851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56851
  have eq56874 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56860 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56860
    | (have j0 := eq56860 (σ X0) X1
       grind)
    | exact resolve eq56860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65775 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23763 (σ x)
       have i₂ := eq23474
       grind)
    | exact superpose eq23474 eq23763
    | exact resolve eq23763 eq23474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23763
  have eq65982 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq65775
  have eq66190 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq502 (σ y) (M.op (σ x) (σ x))
       have i₂ := eq65982
       grind)
    | exact superpose eq65982 eq502
    | exact resolve eq502 eq65982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65982
  have eq66349 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23474 eq66190
    | exact resolve eq66190 eq23474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23474 eq66190
  have eq66415 : y = (k y (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66349 eq32811
    | exact resolve eq32811 eq66349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32811
  have eq66440 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq85 (σ y) x
       have i₂ := eq66349
       grind)
    | exact superpose eq66349 eq85
    | (have r₁ := eq85 (σ y) x
       have r₂ := eq66349
       grind)
    | exact resolve eq85 eq66349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq66349
  have eq66569 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq66440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66440
  have eq66627 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66415
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq66415
    | exact resolve eq66415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66415
  have eq66663 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56860 y X0
       have i₂ := eq66627
       grind)
    | exact superpose eq66627 eq56860
    | (have j0 := eq56860 y X0
       grind)
    | (have r₁ := eq56860 y x
       have r₂ := eq66627
       grind)
    | exact resolve eq56860 eq66627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66627
  have eq66678 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq66663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66663
  have eq67630 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq66569 (σ X0)
       grind)
    | exact superpose eq66569 eq15
    | exact resolve eq15 eq66569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66569
  have eq67652 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66678 eq67630
    | exact resolve eq67630 eq66678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66678 eq67630
  have eq68426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67652 x
       grind)
    | exact superpose eq67652 eq16
    | (have r₁ := eq16
       have r₂ := eq67652 x
       grind)
    | exact resolve eq16 eq67652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67652
  have eq68587 : y = (M.op x y) := by grind
  clear eq68426
  have eq68772 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68587
       grind)
    | exact superpose eq68587 eq16
    | exact resolve eq16 eq68587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68780 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq502 x y
       have i₂ := eq68587
       grind)
    | exact superpose eq68587 eq502
    | exact resolve eq502 eq68587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69288 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op (M.op X0 y) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq897 y x x
       have i₂ := eq68780
       grind)
    | exact superpose eq68780 eq897
    | exact resolve eq897 eq68780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq68780
  have eq69390 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq69288 X0
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq69288
    | exact resolve eq69288 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq69288
  have eq69833 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq69390 x
       have i₂ := eq68587
       grind)
    | exact superpose eq68587 eq69390
    | exact resolve eq69390 eq68587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69390
  have eq70197 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq502 y (M.op x x)
       have i₂ := eq69833
       grind)
    | exact superpose eq69833 eq502
    | exact resolve eq502 eq69833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq69833
  have eq70351 : y = (M.op y y) := by
    first
    | (have i₁ := eq70197
       have i₂ := eq68587
       grind)
    | exact superpose eq68587 eq70197
    | exact resolve eq70197 eq68587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70197
  have eq70393 : y = (k y y) := by
    first
    | (have i₁ := eq18335
       have i₂ := eq70351
       grind)
    | exact superpose eq70351 eq18335
    | exact resolve eq18335 eq70351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18335 eq70351
  have eq70586 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq56860 y X0
       have i₂ := eq70393
       grind)
    | exact superpose eq70393 eq56860
    | (have j0 := eq56860 y X0
       grind)
    | (have r₁ := eq56860 y x
       have r₂ := eq70393
       grind)
    | exact resolve eq56860 eq70393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56860
  have eq70587 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56874 y X0
       have i₂ := eq70393
       grind)
    | exact superpose eq70393 eq56874
    | (have j0 := eq56874 y X0
       grind)
    | exact resolve eq56874 eq70393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56874 eq70393
  have eq70600 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq70587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70587
  have eq70601 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq70586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70586
  have eq71595 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq70600 (σ X0)
       grind)
    | exact superpose eq70600 eq15
    | exact resolve eq15 eq70600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70600
  have eq71623 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq71595 X0
       have i₂ := eq70601 X0
       grind)
    | exact superpose eq70601 eq71595
    | exact resolve eq71595 eq70601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70601 eq71595
  have eq72904 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq68772
       have i₂ := eq71623 x
       grind)
    | exact superpose eq71623 eq68772
    | exact resolve eq68772 eq71623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68772 eq71623
  have eq73181 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq72904
       have i₂ := eq68587
       grind)
    | exact superpose eq68587 eq72904
    | exact resolve eq72904 eq68587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68587 eq72904
  have eq73182 : False := by grind
  exact eq73182

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq74 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq53
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq102 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44
    | exact resolve eq44 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X0
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq111 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq234 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq641 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq111 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq111
    | (have j0 := eq111 (τ X0)
       grind)
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq642 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq641 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq641
    | (have j0 := eq641 X0
       grind)
    | exact resolve eq641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq642 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq642
    | (have j0 := eq642 X0
       grind)
    | exact resolve eq642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq819 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq109 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq109
    | (have j0 := eq109 (τ X0)
       grind)
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq842 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq819 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq819
    | (have j0 := eq819 X0
       grind)
    | exact resolve eq819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq849 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq842 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq842
    | (have j0 := eq842 X0
       grind)
    | exact resolve eq842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1644 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (k (τ X0) (τ X0))
       have i₂ := eq849 (τ X0)
       grind)
    | exact superpose eq849 eq71
    | (have j0 := eq71 X0 (k (τ X0) (τ X0))
       have j1 := eq849 (τ X0)
       grind)
    | exact resolve eq71 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq849
  have eq1666 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1675 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1666 X0
       have j1 := eq645 (τ X0)
       grind)
    | (have r₁ := eq1666 X0
       have r₂ := eq645 (τ X0)
       grind)
    | exact resolve eq1666 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq1666
  have eq1680 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1675 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1675
    | (have j0 := eq1675 X0
       grind)
    | exact resolve eq1675 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1681 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1680 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1680
    | (have j0 := eq1680 X0
       grind)
    | exact resolve eq1680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq4823 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74 X0 (σ X0) (σ X0)
       have i₂ := eq1681 (σ X0)
       grind)
    | exact superpose eq1681 eq74
    | (have j1 := eq1681 (σ X0)
       grind)
    | exact resolve eq74 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1681
  have eq4845 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4823 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4823
    | (have j0 := eq4823 X0
       grind)
    | exact resolve eq4823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823
  have eq4864 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4845 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4845
    | (have j0 := eq4845 X0
       grind)
    | exact resolve eq4845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845
  have eq4888 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq4864
  have eq4912 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq5055 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4912 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq4912
    | (have j0 := eq4912 X0
       grind)
    | exact resolve eq4912 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq5173 : ∀ X0 X1 : G, (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) = (σ (k (τ (k X0 X1)) (τ (k X0 X1)))) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 (τ X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq102
    | (have j0 := eq102 X0 (τ X1)
       grind)
    | exact resolve eq102 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq102
  have eq5232 : ∀ X0 X1 : G, (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) = (k (σ (τ (k X0 X1))) (k X0 X1)) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5173 X0 X1
       have i₂ := eq19 (k X0 X1) (τ (k X0 X1))
       grind)
    | exact superpose eq19 eq5173
    | (have j0 := eq5173 X0 X1
       grind)
    | exact resolve eq5173 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173
  have eq5242 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5232 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5232
    | (have j0 := eq5232 X0 X1
       grind)
    | exact resolve eq5232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5232
  have eq5246 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5242 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5242
    | (have j0 := eq5242 X0 X1
       grind)
    | exact resolve eq5242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5242
  have eq5247 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5246 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5246
    | (have j0 := eq5246 X0 X1
       grind)
    | exact resolve eq5246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5248 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5247 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq5247 X0 X1
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq5247 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247
  have eq5656 : ∀ X0 X1 X2 : G, (k X2 (σ (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (σ (τ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k (τ X0) X1)
       have i₂ := eq234 X0 X1 (τ X2)
       grind)
    | exact superpose eq234 eq18
    | (have j1 := eq234 X0 X1 (τ X2)
       grind)
    | exact resolve eq18 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq5699 : ∀ X0 X1 X2 : G, (k X2 (σ (k (τ X0) X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5656 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq5656
    | (have j0 := eq5656 X0 X1 X2
       grind)
    | exact resolve eq5656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq5723 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5699 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq5699
    | (have j0 := eq5699 X0 X1 X2
       grind)
    | exact resolve eq5699 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5699
  have eq5739 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5723 X0 X1 X2
       have j1 := eq12 X2 (k X0 (σ X1))
       grind)
    | (have r₁ := eq5723 X0 X1 X2
       have r₂ := eq12 X0 (k X0 (σ X1))
       grind)
    | exact resolve eq5723 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq5751 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5739 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq5739
    | (have j0 := eq5739 X0 X1 X2
       grind)
    | exact resolve eq5739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5739
  have eq5973 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5248 X0 (M.op X0 X0)
       have i₂ := eq5055 X0
       grind)
    | exact superpose eq5055 eq5248
    | (have j1 := eq5055 X0
       grind)
    | exact resolve eq5248 eq5055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq6027 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5973 X0
       have j1 := eq32 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq5973 X0
       have r₂ := eq32 X0 x
       grind)
    | exact resolve eq5973 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq5973
  have eq6040 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6027 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq6027
    | exact resolve eq6027 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6027
  have eq6227 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5248 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq6040 X0
       grind)
    | exact superpose eq6040 eq5248
    | exact resolve eq5248 eq6040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248
  have eq6291 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6227 (σ X0)
       grind)
    | exact superpose eq6227 eq15
    | exact resolve eq15 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6320 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6291 X0
       have i₂ := eq6227 X0
       grind)
    | exact superpose eq6227 eq6291
    | exact resolve eq6291 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6227 eq6291
  have eq12790 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op (k X2 X0) X1) ∨ (k X2 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5751 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5751
    | exact resolve eq5751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq36216 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12790 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq6040 X0
       grind)
    | exact superpose eq6040 eq12790
    | (have j0 := eq12790 X0 (M.op X0 X1) X1
       grind)
    | exact resolve eq12790 eq6040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040 eq12790
  have eq36391 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq36216 (τ X0) X1
       grind)
    | exact superpose eq36216 eq19
    | (have j1 := eq36216 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq36216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq36418 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq36216 (σ X0) (σ X1)
       grind)
    | exact superpose eq36216 eq15
    | (have j1 := eq36216 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq36216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36216
  have eq36850 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36391 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36391
    | exact resolve eq36391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36391
  have eq36995 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36850 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq36850
    | (have j0 := eq36850 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq36850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36850
  have eq39414 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36418 x y
       grind)
    | exact superpose eq36418 eq16
    | (have j1 := eq36418 x y
       grind)
    | exact resolve eq16 eq36418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36418
  have eq39924 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39414
       have i₂ := eq36995 x y
       grind)
    | exact superpose eq36995 eq39414
    | (have j1 := eq36995 (σ x) (σ y)
       grind)
    | (have r₁ := eq39414
       have r₂ := eq36995 x y
       grind)
    | (have r₁ := eq39414
       have r₂ := eq36995 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq39414
       have r₂ := eq36995 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq39414 eq36995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36995 eq39414
  have eq39927 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq39924
  have eq39930 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39927
       grind)
    | exact superpose eq39927 eq16
    | exact resolve eq16 eq39927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39927
  have eq39931 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq39930
       have r₂ := eq6320 x
       grind)
    | exact resolve eq39930 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39930
  have eq40947 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39931
       grind)
    | exact superpose eq39931 eq16
    | exact resolve eq16 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40948 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq39931
       grind)
    | exact superpose eq39931 eq10
    | exact resolve eq10 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39931
  have eq41025 : x = y := by
    first
    | (have i₁ := eq40948
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40948
    | exact resolve eq40948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40948
  have eq41026 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq40947
       have i₂ := eq6320 x
       grind)
    | exact superpose eq6320 eq40947
    | exact resolve eq40947 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320 eq40947
  have eq41035 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq41026
       have i₂ := eq41025
       grind)
    | exact superpose eq41025 eq41026
    | exact resolve eq41026 eq41025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41025 eq41026
  have eq41036 : False := by grind
  exact eq41036

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq32 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq155 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq214 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 X1 X2 (M.op X1 X1)
       have i₂ := eq32 X1
       grind)
    | exact superpose eq32 eq31
    | exact resolve eq31 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 X2 (M.op X0 X1) X1
       have i₂ := eq34 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq34 eq31
    | exact resolve eq31 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X2 (M.op X0 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X3
       have i₂ := eq31 X0 X0 X2 X1
       grind)
    | exact superpose eq31 eq42
    | exact resolve eq42 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq42
  have eq650 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq487 X1 X2 (M.op X1 X2) (M.op x (M.op (M.op X1 X2) x))
       have i₂ := eq9 (M.op X1 X2) x x
       grind)
    | exact superpose eq9 eq487
    | exact resolve eq487 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq702 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq650 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq650
    | exact resolve eq650 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X1 X0)
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq32
    | exact resolve eq32 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2004 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X0 X1 X2
       have i₂ := eq702 X0 X1
       grind)
    | exact superpose eq702 eq214
    | exact resolve eq214 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq2101 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq650 (M.op X0 X1) (M.op X1 (M.op X2 X1))
       have i₂ := eq2004 X1 X2 X0
       grind)
    | exact superpose eq2004 eq650
    | exact resolve eq650 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq2004
  have eq2105 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2101 X0 X1 X2
       have i₂ := eq702 X1 X0
       grind)
    | exact superpose eq702 eq2101
    | exact resolve eq2101 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq2101
  have eq3030 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq226 X0 X1 X2
       have i₂ := eq2105 X0 X1 X0
       grind)
    | exact superpose eq2105 eq226
    | exact resolve eq226 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3042 : ∀ X1 X3 : G, (M.op X3 (M.op (M.op X1 X1) X3)) = (M.op X1 (M.op (M.op X1 X1) X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq3030 (M.op X1 X1) X3 (M.op x (M.op X1 x))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq3030
    | exact resolve eq3030 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4279 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3042 X1 (M.op X0 X1)
       have i₂ := eq2105 X0 X1 X1
       grind)
    | exact superpose eq2105 eq3042
    | exact resolve eq3042 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105 eq3042
  have eq4380 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4279 X0 X1
       have i₂ := eq1127 X0 X1
       grind)
    | exact superpose eq1127 eq4279
    | exact resolve eq4279 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq4279
  have eq4600 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4380 X2 X1
       have i₂ := eq3030 X1 X2 X0
       grind)
    | (have i₁ := eq4380 (M.op X2 X0) X0
       have i₂ := eq3030 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq3030 eq4380
    | exact resolve eq4380 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030 eq4380
  have eq5580 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0))) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4600 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq4600 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq4600
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq4600 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq5747 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5580 X0 X1 x
       have i₂ := eq34 X0 x
       grind)
    | exact superpose eq34 eq5580
    | (have j0 := eq5580 X0 X1 x
       grind)
    | exact resolve eq5580 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq5580
  have eq5778 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5747 X0 X1
       have j1 := eq155 X0 X1
       grind)
    | (have r₁ := eq5747 X0 X1
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq5747 X0 X0
       have r₂ := eq155 X0 X0
       grind)
    | (have r₁ := eq5747 (M.op X0 X0) (M.op X1 X0)
       have r₂ := eq155 X0 X1
       grind)
    | exact resolve eq5747 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq5747
  have eq5811 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5778 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5778
    | (have j0 := eq5778 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq5778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5825 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq5778 X0 (τ X1)
       grind)
    | exact superpose eq5778 eq19
    | (have j1 := eq5778 (k (σ X0) X1) (σ (M.op (τ X1) X0))
       grind)
    | exact resolve eq19 eq5778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5778
  have eq5934 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5825 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5825
    | exact resolve eq5825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5825
  have eq5988 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5934 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5934
    | (have j0 := eq5934 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq5934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5934
  have eq10516 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5811 y x
       grind)
    | exact superpose eq5811 eq16
    | (have j1 := eq5811 x y
       grind)
    | exact resolve eq16 eq5811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5811
  have eq10782 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10516
       have i₂ := eq5988 x y
       grind)
    | exact superpose eq5988 eq10516
    | (have j1 := eq5988 (σ x) (σ y)
       grind)
    | (have r₁ := eq10516
       have r₂ := eq5988 x y
       grind)
    | (have r₁ := eq10516
       have r₂ := eq5988 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10516
       have r₂ := eq5988 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10516 eq5988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988 eq10516
  have eq10783 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10782
  have eq10789 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10783
       grind)
    | exact superpose eq10783 eq10
    | exact resolve eq10 eq10783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10783
  have eq10838 : x = y ∨ x = y := by
    first
    | (have i₁ := eq10789
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10789
    | exact resolve eq10789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10789
  have eq10839 : x = y := by grind
  clear eq10838
  have eq10841 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10839
       grind)
    | exact superpose eq10839 eq16
    | exact resolve eq16 eq10839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10839
  have eq10842 : False := by grind
  exact eq10842

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq43 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq45 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq129 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq42 X1 X4 X0 X2
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq648 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq42 X1 X1 X0 X2
       grind)
    | exact superpose eq42 eq53
    | exact resolve eq53 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq53
  have eq801 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq648 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq43 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq648
    | exact resolve eq648 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq844 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq801 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq801
    | exact resolve eq801 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq801 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq801
    | exact resolve eq801 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq801
  have eq899 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq844 X0 X1 X2
       have i₂ := eq845 (M.op X0 X2) X1
       grind)
    | exact superpose eq845 eq844
    | exact resolve eq844 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq1087 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0)
       have i₂ := eq845 X0 X1
       grind)
    | exact superpose eq845 eq43
    | exact resolve eq43 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X0 X1
       have i₂ := eq899 X1 X0 X0
       grind)
    | exact superpose eq899 eq1087
    | exact resolve eq1087 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1087
  have eq1272 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X1 X0 X1 X0 X2
       have i₂ := eq1123 X1 X0
       grind)
    | exact superpose eq1123 eq129
    | exact resolve eq129 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1123
  have eq1358 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1272 X0 X1 X2
       have i₂ := eq845 X0 X2
       grind)
    | exact superpose eq845 eq1272
    | exact resolve eq1272 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq1272
  have eq1739 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1358 X0 (M.op X0 X0) X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq1358
    | exact resolve eq1358 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1358
  have eq1991 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq1739 X1 X0
       grind)
    | exact superpose eq1739 eq9
    | exact resolve eq9 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq4099 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq179
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq179
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq179
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq179
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq179 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4100 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4099
  have eq77896 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4100
       grind)
    | exact superpose eq4100 eq16
    | exact resolve eq16 eq4100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100
  have eq77897 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq77896
       have r₂ := eq22 x
       grind)
    | exact resolve eq77896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77896
  have eq2000054 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq77897
       grind)
    | exact superpose eq77897 eq22
    | exact resolve eq22 eq77897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77897
  have eq2000594 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2000054
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq2000054
    | exact resolve eq2000054 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000054
  have eq2000595 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq2000594
  have eq2000893 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2000595
       grind)
    | exact superpose eq2000595 eq10
    | exact resolve eq10 eq2000595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000595
  have eq2001673 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2000893
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2000893
    | exact resolve eq2000893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000893
  have eq2001674 : (M.op x x) = (M.op y y) := by grind
  clear eq2001673
  have eq2002847 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x x)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1991 y y x
       have i₂ := eq2001674
       grind)
    | exact superpose eq2001674 eq1991
    | exact resolve eq1991 eq2001674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991 eq2001674
  have eq2003337 : x = y := by
    first
    | (have i₁ := eq2002847 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq2002847
    | exact resolve eq2002847 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002847
  have eq2004501 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2003337
       grind)
    | exact superpose eq2003337 eq16
    | exact resolve eq16 eq2003337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003337
  have eq2004502 : False := by grind
  exact eq2004502

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
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
  have eq101 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
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
  have eq106 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
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
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq140 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130 x y
       grind)
    | exact superpose eq130 eq16
    | (have j1 := eq130 x y
       grind)
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq156 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq26
    | exact resolve eq26 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ (M.op X0 X0))
       have i₂ := eq156 X0
       grind)
    | exact superpose eq156 eq9
    | exact resolve eq9 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq309 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq308
    | exact resolve eq308 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq308
  have eq322 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq309 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq309
    | exact resolve eq309 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq327 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq322
    | exact resolve eq322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq330 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq378 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq330 X0 X0
       grind)
    | exact superpose eq330 eq9
    | exact resolve eq9 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op X0 X0)
       have i₂ := eq330 X0 X0
       grind)
    | exact superpose eq330 eq26
    | exact resolve eq26 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq380 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq380
    | exact resolve eq380 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq140
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq140
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq775 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq774
  have eq783 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1 (M.op X0 X0)
       have i₂ := eq330 X0 X0
       grind)
    | exact superpose eq330 eq378
    | exact resolve eq378 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq378 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq25 X1 X1 X0 X2
       grind)
    | exact superpose eq25 eq378
    | exact resolve eq378 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq378
  have eq1354 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq784 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq784
    | exact resolve eq784 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq330 X0 X1
       grind)
    | exact superpose eq330 eq1354
    | exact resolve eq1354 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1878 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X0 X1 X2
       have i₂ := eq1400 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq1400 eq101
    | exact resolve eq101 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq2024 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1878 X0 X1 (M.op X0 X0)
       have i₂ := eq330 X0 X0
       grind)
    | exact superpose eq330 eq1878
    | exact resolve eq1878 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq1878
  have eq2166 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq784 X3 X1 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq2024 X1 X0
       grind)
    | exact superpose eq2024 eq784
    | exact resolve eq784 eq2024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq2024
  have eq3579 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq106 X0 X1 X2 X3 X4 X5
       have i₂ := eq1400 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq1400 eq106
    | exact resolve eq106 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq3920 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3579 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq26 (M.op X1 X2)
       grind)
    | exact superpose eq26 eq3579
    | exact resolve eq3579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3579
  have eq4006 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3920 X0 X1 X2 X3
       have i₂ := eq783 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq783 eq3920
    | exact resolve eq3920 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq4033 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4006 X0 X1 X2 X3
       have i₂ := eq1400 X1 X0
       grind)
    | exact superpose eq1400 eq4006
    | exact resolve eq4006 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq4006
  have eq7285 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4033 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq4033
    | exact resolve eq4033 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4033
  have eq7560 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7285 X0 X1 X2 X3 X4
       have i₂ := eq783 X0 X0
       grind)
    | exact superpose eq783 eq7285
    | exact resolve eq7285 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7285
  have eq13974 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq775
       grind)
    | exact superpose eq775 eq16
    | exact resolve eq16 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq13975 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq13974
       have r₂ := eq23 x
       grind)
    | exact resolve eq13974 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13974
  have eq119102 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 (M.op X1 (M.op X2 x))) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7560 y X1 y x x
       have i₂ := eq13975
       grind)
    | exact superpose eq13975 eq7560
    | exact resolve eq7560 eq13975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7560 eq13975
  have eq119136 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq119102 x x x
       have i₂ := eq2166 x x x x
       grind)
    | exact superpose eq2166 eq119102
    | exact resolve eq119102 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq119102
  have eq213609 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq77 x x
       have i₂ := eq119136
       grind)
    | exact superpose eq119136 eq77
    | exact resolve eq77 eq119136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq119136
  have eq213970 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq213609 x
       have i₂ := eq783 (σ y) x
       grind)
    | exact superpose eq783 eq213609
    | exact resolve eq213609 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq213609
  have eq213972 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq213970
       have i₂ := eq23 y
       grind)
    | exact superpose eq23 eq213970
    | exact resolve eq213970 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213970
  have eq213973 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq213972
  have eq214881 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq213973
       grind)
    | exact superpose eq213973 eq10
    | exact resolve eq10 eq213973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213973
  have eq215232 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq214881
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq214881
    | exact resolve eq214881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214881
  have eq215235 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq215232
       grind)
    | exact superpose eq215232 eq16
    | exact resolve eq16 eq215232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215232
  have eq215236 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq215235
       have r₂ := eq23 x
       grind)
    | exact resolve eq215235 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq215235
  have eq216299 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq395 y
       have i₂ := eq215236
       grind)
    | exact superpose eq215236 eq395
    | exact resolve eq395 eq215236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq216363 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq215236
       grind)
    | exact superpose eq215236 eq10
    | exact resolve eq10 eq215236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215236
  have eq216809 : x = (M.op y y) := by
    first
    | (have i₁ := eq216363
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq216363
    | exact resolve eq216363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216363
  have eq216974 : x = (M.op x y) := by
    first
    | (have i₁ := eq380 y
       have i₂ := eq216809
       grind)
    | exact superpose eq216809 eq380
    | exact resolve eq380 eq216809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq216809
  have eq265193 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq216299
       grind)
    | exact superpose eq216299 eq16
    | exact resolve eq16 eq216299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216299
  have eq265526 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq265193
       have i₂ := eq216974
       grind)
    | exact superpose eq216974 eq265193
    | exact resolve eq265193 eq216974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216974 eq265193
  have eq265527 : False := by grind
  exact eq265527

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation1924 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
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
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X0)) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq122 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq636 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq16
    | (have j1 := eq120 x y
       grind)
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq120 X0 X1
       grind)
    | exact superpose eq120 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq120 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq120 X0 X1
       grind)
    | exact resolve eq13 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq646 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq647 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq646 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq646 X0 X1
       have r₂ := eq13 (σ (k X0 X1)) (σ X1)
       grind)
    | (have r₁ := eq646 X0 X1
       have r₂ := eq13 (σ X1) (σ (k X0 X1))
       grind)
    | (have r₁ := eq646 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq646 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq653 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq647
    | (have j0 := eq647 X0 X1
       grind)
    | exact resolve eq647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq656 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq653
    | (have j0 := eq653 X0 X1
       grind)
    | exact resolve eq653 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq707 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122
    | exact resolve eq122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq122 X1 X0
       grind)
    | exact superpose eq122 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq122 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq122 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq122 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op (M.op (τ X1) X0) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq9
    | (have j1 := eq122 X1 X0
       grind)
    | exact resolve eq9 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq723 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq727 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq733 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq707
    | (have j0 := eq707 X0 X1
       grind)
    | exact resolve eq707 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq794 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq645
    | (have j0 := eq645 (τ X0) (τ X1)
       grind)
    | exact resolve eq645 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq802 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq794
    | (have j0 := eq794 X0 X1
       grind)
    | exact resolve eq794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq805 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq802
    | (have j0 := eq802 X0 X1
       grind)
    | exact resolve eq802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq807 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq805
    | (have j0 := eq805 X0 X1
       grind)
    | exact resolve eq805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq808 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq807 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq807
    | (have j0 := eq807 X0 X1
       grind)
    | exact resolve eq807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq809 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq808
    | (have j0 := eq808 X0 X1
       grind)
    | exact resolve eq808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq810 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq809
    | (have j0 := eq809 X0 X1
       grind)
    | exact resolve eq809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq3699 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq656 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq656
    | (have j0 := eq656 (τ (k X0 X1)) (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq656 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq656
  have eq3749 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3699 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3699
    | (have j0 := eq3699 X0 X1
       grind)
    | exact resolve eq3699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3772 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3749 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3749
    | (have j0 := eq3749 X0 X1
       grind)
    | exact resolve eq3749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3749
  have eq3790 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3772 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq3772
    | (have j0 := eq3772 X0 X1
       grind)
    | exact resolve eq3772 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3772
  have eq3807 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3790 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3790
    | (have j0 := eq3790 X0 X1
       grind)
    | exact resolve eq3790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq3820 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3807 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3807
    | (have j0 := eq3807 X0 X1
       grind)
    | exact resolve eq3807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3807
  have eq3833 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3820 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3820
    | (have j0 := eq3820 X0 X1
       grind)
    | exact resolve eq3820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3820
  have eq5643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq636
       have i₂ := eq733 x y
       grind)
    | exact superpose eq733 eq636
    | (have j1 := eq733 (σ x) (σ y)
       grind)
    | (have r₁ := eq636
       have r₂ := eq733 x y
       grind)
    | (have r₁ := eq636
       have r₂ := eq733 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq636
       have r₂ := eq733 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq636 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq5644 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5643
  have eq5646 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5644
       grind)
    | exact superpose eq5644 eq16
    | exact resolve eq16 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq5647 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5646
       have r₂ := eq22 x
       grind)
    | exact resolve eq5646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646
  have eq5648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq5647
       grind)
    | exact superpose eq5647 eq9
    | exact resolve eq9 eq5647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5659 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5648
       grind)
    | exact superpose eq5648 eq16
    | exact resolve eq16 eq5648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5648
  have eq5681 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5659
       have i₂ := eq5647
       grind)
    | exact superpose eq5647 eq5659
    | exact resolve eq5659 eq5647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5647 eq5659
  have eq5702 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5681
  have eq5703 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5702
  have eq5710 : (σ x) = (σ y) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq5703
       grind)
    | exact superpose eq5703 eq9
    | exact resolve eq9 eq5703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq5725 : y = (τ (σ x)) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5710
       grind)
    | exact superpose eq5710 eq10
    | exact resolve eq10 eq5710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5710
  have eq5777 : x = y ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5725
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5725
    | exact resolve eq5725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725
  have eq5779 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5777
       grind)
    | exact superpose eq5777 eq16
    | exact resolve eq16 eq5777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5777
  have eq5780 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have r₁ := eq5779
       have r₂ := eq22 x
       grind)
    | exact resolve eq5779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5779
  have eq5843 : y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq5780
       grind)
    | exact superpose eq5780 eq9
    | exact resolve eq9 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5845 : y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq108 (σ y) (σ x)
       have i₂ := eq5780
       grind)
    | exact superpose eq5780 eq108
    | exact resolve eq108 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5780
  have eq7411 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq725
    | exact resolve eq725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq7494 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7411 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7411
    | (have j0 := eq7411 X0 X1
       grind)
    | exact resolve eq7411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7411
  have eq7560 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op (M.op X0 X1) X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq7494 X0 X1
       grind)
    | exact superpose eq7494 eq10
    | (have j1 := eq7494 X0 X1
       grind)
    | exact resolve eq10 eq7494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq7618 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7560 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq7560
    | (have j0 := eq7560 X0 X1
       grind)
    | exact resolve eq7560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7560
  have eq7699 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X1)
       have i₂ := eq7618 X0 X1
       grind)
    | exact superpose eq7618 eq9
    | (have j1 := eq7618 X1 X0
       grind)
    | exact resolve eq9 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7822 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7699 X0 X1
       have i₂ := eq7618 X1 X0
       grind)
    | exact superpose eq7618 eq7699
    | (have j0 := eq7699 X0 X1
       have j1 := eq7618 X1 X0
       grind)
    | exact resolve eq7699 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7618 eq7699
  have eq7868 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7822 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7822
  have eq7940 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7868 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7868
  have eq7941 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7940
  have eq7970 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3833 (M.op X0 X0) X0
       have i₂ := eq7941 X0
       grind)
    | exact superpose eq7941 eq3833
    | (have j0 := eq3833 (M.op X0 X0) (M.op (M.op X0 X0) X0)
       have j1 := eq7941 X0
       grind)
    | exact resolve eq3833 eq7941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833 eq7941
  have eq8007 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7970
  have eq11977 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq727
    | exact resolve eq727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq12069 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11977 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11977
    | (have j0 := eq11977 X0 X1
       grind)
    | exact resolve eq11977 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11977
  have eq12205 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq12069 X0 X1
       grind)
    | exact superpose eq12069 eq10
    | (have j1 := eq12069 X0 X1
       grind)
    | exact resolve eq10 eq12069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12069
  have eq12265 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12205 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq12205
    | (have j0 := eq12205 X0 X1
       grind)
    | exact resolve eq12205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12205
  have eq12465 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265
  have eq14401 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq8007 y
       have i₂ := eq5843
       grind)
    | exact superpose eq5843 eq8007
    | (have j0 := eq8007 y
       grind)
    | (have r₁ := eq8007 y
       have r₂ := eq5843
       grind)
    | exact resolve eq8007 eq5843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5843
  have eq14402 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq8007 y
       have i₂ := eq5845
       grind)
    | exact superpose eq5845 eq8007
    | (have j0 := eq8007 y
       grind)
    | (have r₁ := eq8007 y
       have r₂ := eq5845
       grind)
    | exact resolve eq8007 eq5845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5845 eq8007
  have eq14472 : y ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by grind
  clear eq14402
  have eq14473 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq14472
  have eq14474 : y ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq14401
  have eq14475 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq14474
  have eq16413 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14473
       have i₂ := eq14475
       grind)
    | exact superpose eq14475 eq14473
    | exact resolve eq14473 eq14475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14473 eq14475
  have eq16457 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq16413
  have eq16472 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16457
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq16457
    | exact resolve eq16457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16457
  have eq16531 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq16472
       grind)
    | exact superpose eq16472 eq10
    | exact resolve eq10 eq16472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16472
  have eq16593 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16531
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16531
    | exact resolve eq16531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531
  have eq16594 : y = (M.op y y) := by grind
  clear eq16593
  have eq16650 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq12465 X0 y
       have i₂ := eq16594
       grind)
    | exact superpose eq16594 eq12465
    | (have j0 := eq12465 y (k X0 y)
       grind)
    | exact resolve eq12465 eq16594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq16768 : ∀ X0 : G, y ≠ y ∨ y = (k (τ X0) y) ∨ (τ X0) = y ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq16650 (τ X0)
       have i₂ := eq122 X0 y
       grind)
    | exact superpose eq122 eq16650
    | (have j0 := eq16650 (τ X0)
       have j1 := eq122 X0 y
       grind)
    | (have r₁ := eq16650 (τ X0)
       have r₂ := eq122 X0 y
       grind)
    | exact resolve eq16650 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq16650
  have eq16771 : ∀ X0 : G, y ≠ y ∨ y = (k (τ X0) y) ∨ (τ X0) = y ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have j0 := eq16768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16768
  have eq16772 : ∀ X0 : G, y = (k (τ X0) y) ∨ (τ X0) = y ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have j0 := eq16771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16771
  have eq18813 : ∀ X0 : G, y = (k X0 y) ∨ y = X0 ∨ (k (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq16772 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16772
    | exact resolve eq16772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16772
  have eq18902 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ y = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq18813 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq18813
    | (have j0 := eq18813 X0
       grind)
    | exact resolve eq18813 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18813
  have eq18958 : ∀ X0 : G, (k X0 y) = (τ (σ (M.op X0 y))) ∨ y = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 y)
       have i₂ := eq18902 X0
       grind)
    | exact superpose eq18902 eq10
    | (have j1 := eq18902 X0
       grind)
    | exact resolve eq10 eq18902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18902
  have eq19023 : ∀ X0 : G, y = (k X0 y) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq18958 X0
       have i₂ := eq10 (M.op X0 y)
       grind)
    | exact superpose eq10 eq18958
    | (have j0 := eq18958 X0
       grind)
    | exact resolve eq18958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18958
  have eq19155 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq19023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19023
  have eq19187 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq19155 X0
       have j1 := eq14 X0 y
       grind)
    | (have r₁ := eq19155 X0
       have r₂ := eq14 X0 y
       grind)
    | (have r₁ := eq19155 X0
       have r₂ := eq14 y (M.op X0 y)
       grind)
    | (have r₁ := eq19155 X0
       have r₂ := eq14 (M.op X0 y) y
       grind)
    | exact resolve eq19155 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19155
  have eq19585 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq636
       have i₂ := eq19187 x
       grind)
    | exact superpose eq19187 eq636
    | (have j1 := eq19187 x
       grind)
    | exact resolve eq636 eq19187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq19187
  have eq19603 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19585
  have eq20264 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq19603
       grind)
    | exact superpose eq19603 eq16
    | exact resolve eq16 eq19603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20269 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19603
       grind)
    | exact superpose eq19603 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19603
       grind)
    | exact resolve eq13 eq19603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19603
  have eq20286 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq20269
  have eq20287 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq20286
  have eq20294 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20287
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq20287
    | exact resolve eq20287 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20287
  have eq20298 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20294
       have i₂ := eq16594
       grind)
    | exact superpose eq16594 eq20294
    | exact resolve eq20294 eq16594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16594 eq20294
  have eq20300 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq20298
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20298
    | exact resolve eq20298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20298
  have eq20362 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20300
       grind)
    | exact superpose eq20300 eq10
    | exact resolve eq10 eq20300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20300
  have eq20427 : x = y ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq20362
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20362
    | exact resolve eq20362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20362
  have eq20428 : (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq20427
  have eq20459 : (k x y) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq20428
       grind)
    | exact superpose eq20428 eq10
    | exact resolve eq10 eq20428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20428
  have eq20535 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq20459
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq20459
    | exact resolve eq20459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20459
  have eq20575 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq810 x y
       have i₂ := eq20535
       grind)
    | exact superpose eq20535 eq810
    | (have j0 := eq810 x y
       grind)
    | (have r₁ := eq810 x y
       have r₂ := eq20535
       grind)
    | exact resolve eq810 eq20535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq20535
  have eq20601 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq20575
  have eq20602 : y = (M.op x y) ∨ x = y := by grind
  clear eq20601
  have eq20641 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq20264
       have i₂ := eq20602
       grind)
    | exact superpose eq20602 eq20264
    | exact resolve eq20264 eq20602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20264 eq20602
  have eq20665 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20641
  have eq20666 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq20665
  have eq20692 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20666
       grind)
    | exact superpose eq20666 eq10
    | exact resolve eq10 eq20666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20666
  have eq20757 : x = y ∨ x = y := by
    first
    | (have i₁ := eq20692
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20692
    | exact resolve eq20692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20692
  have eq20758 : x = y := by grind
  clear eq20757
  have eq20763 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20758
       grind)
    | exact superpose eq20758 eq16
    | exact resolve eq16 eq20758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20758
  have eq20860 : False := by grind
  exact eq20860

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyx_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq341 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq341 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq341 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq341 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq360 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq377 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq360 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq360
    | exact resolve eq360 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq360
  have eq408 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (σ X0)
       have i₂ := eq377 X0
       grind)
    | exact superpose eq377 eq9
    | exact resolve eq9 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq377 X0
       grind)
    | exact superpose eq377 eq9
    | exact resolve eq9 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (σ (σ (M.op X0 X0)))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq408 (M.op x (σ (M.op X0 X0))) X1 X3
       have i₂ := eq408 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq408 eq408
    | exact resolve eq408 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq788 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq788 (σ X0) (σ X1)
       grind)
    | exact superpose eq788 eq15
    | (have j1 := eq788 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 X1
       have i₂ := eq377 X0
       grind)
    | exact superpose eq377 eq852
    | (have j0 := eq852 X0 X1
       grind)
    | exact resolve eq852 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq1816 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq788 X0 X1
       grind)
    | exact superpose eq788 eq871
    | (have j0 := eq871 X0 X1
       have j1 := eq788 X0 X1
       grind)
    | exact resolve eq871 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq871
  have eq16271 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op (σ X0) (M.op X1 X1)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X2)) = (σ (M.op X0 X2)) ∨ (M.op X0 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) (σ X0) X1
       have i₂ := eq1816 X0 X2
       grind)
    | exact superpose eq1816 eq9
    | (have j1 := eq1816 X0 X2
       grind)
    | exact resolve eq9 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq16290 : ∀ X0 X2 : G, (M.op (σ X0) (σ X2)) = (σ (M.op X0 X2)) ∨ (σ X0) = (σ X2) ∨ (M.op X0 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq16271 X0 x X2
       have i₂ := eq417 X0 x
       grind)
    | exact superpose eq417 eq16271
    | (have j0 := eq16271 X0 x X2
       grind)
    | exact resolve eq16271 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq16271
  have eq53819 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16290 x y
       grind)
    | exact superpose eq16290 eq16
    | (have j1 := eq16290 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq16290 x y
       grind)
    | exact resolve eq16 eq16290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16290
  have eq53897 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq53819
  have eq53931 : ∀ X0 : G, y = (M.op (M.op x (σ (σ (M.op X0 X0)))) (M.op x x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq452 X0 x y
       have i₂ := eq53897
       grind)
    | exact superpose eq53897 eq452
    | exact resolve eq452 eq53897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53897
  have eq53958 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53931 x
       have i₂ := eq452 x x x
       grind)
    | (have i₁ := eq53931 x
       have i₂ := eq452 x x (M.op (M.op x (σ (σ (M.op x x)))) (M.op x x))
       grind)
    | exact superpose eq452 eq53931
    | exact resolve eq53931 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq53931
  have eq53963 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq53958
       grind)
    | exact superpose eq53958 eq10
    | exact resolve eq10 eq53958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53958
  have eq54103 : x = y ∨ x = y := by
    first
    | (have i₁ := eq53963
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53963
    | exact resolve eq53963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53963
  have eq54104 : x = y := by grind
  clear eq54103
  have eq54107 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54104
       grind)
    | exact superpose eq54104 eq16
    | exact resolve eq16 eq54104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54104
  have eq54108 : False := by grind
  exact eq54108
