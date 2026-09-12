import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_y_pxx_pyy_pxy_Equation1027 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op x (M.op X0 (M.op X1 X0)))) x)
       have i₂ := eq9 (M.op X0 (M.op X1 X0)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 x)
       have i₂ := eq62 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 x)
       have i₂ := eq62 X0 x
       grind)
    | exact superpose eq62 eq14
    | (have j0 := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq83
    | (have j0 := eq83 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq83 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq83 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X2)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X1 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq403 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq412 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = X1 ∨ (M.op X1 (M.op (M.op X0 X1) X2)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 X0 X1 X2
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq394
    | (have j0 := eq394 X0 X1 X2
       grind)
    | exact resolve eq394 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq418 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq404
    | (have j0 := eq404 X0 X1
       grind)
    | exact resolve eq404 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq424 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq381
    | (have j0 := eq381 X0 X1
       grind)
    | exact resolve eq381 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq431 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq418
    | (have j0 := eq418 X0 X1
       grind)
    | exact resolve eq418 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq436 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       have j1 := eq83 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq424 X0 X1
       have r₂ := eq83 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq424 X0 X0
       have r₂ := eq83 X0 X0
       grind)
    | exact resolve eq424 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq616 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 X0
       have i₂ := eq431 X1 X0
       grind)
    | exact superpose eq431 eq62
    | (have j1 := eq431 X1 X0
       grind)
    | exact resolve eq62 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq431 X1 X0
       grind)
    | exact superpose eq431 eq83
    | (have j0 := eq83 X0 X1
       have j1 := eq431 X1 X0
       grind)
    | (have r₁ := eq83 X1 X0
       have r₂ := eq431 X0 X1
       grind)
    | exact resolve eq83 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq431 X0 (M.op X0 X1)
       grind)
    | exact superpose eq431 eq62
    | (have j1 := eq431 X0 (M.op X0 X1)
       grind)
    | exact resolve eq62 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq431 (σ x) (σ y)
       grind)
    | exact superpose eq431 eq16
    | (have j1 := eq431 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq640 : (σ x) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq636
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq636
    | exact resolve eq636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq646 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq640
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq640
    | exact resolve eq640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq946 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq962 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 (M.op X0 X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq946
    | (have j0 := eq946 X0 (M.op X0 X1)
       grind)
    | exact resolve eq946 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq946
  have eq981 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq962 X0 X1
       have j1 := eq436 X0 X1
       grind)
    | (have r₁ := eq962 X0 X1
       have r₂ := eq436 X0 X1
       grind)
    | exact resolve eq962 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1032 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1044 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1032 X0 X1
       have j1 := eq436 X0 X1
       grind)
    | (have r₁ := eq1032 X0 X1
       have r₂ := eq436 X0 X1
       grind)
    | exact resolve eq1032 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq1032
  have eq1050 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1044 X1 X0
       have i₂ := eq415 X1 X0
       grind)
    | exact superpose eq415 eq1044
    | (have j1 := eq415 X1 X0
       grind)
    | exact resolve eq1044 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq1053 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1044 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq1044
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq1044 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1071 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1050 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1080 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1053 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq1053
    | (have j0 := eq1053 X0 X1
       grind)
    | exact resolve eq1053 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1081 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1080 X0 X1
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq1080 X1 X0
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq1080 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1080
  have eq1405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1071 (σ X0) (σ X1)
       grind)
    | exact superpose eq1071 eq15
    | (have j1 := eq1071 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1071 (τ X0) X1
       grind)
    | exact superpose eq1071 eq17
    | (have j1 := eq1071 (τ X0) X1
       grind)
    | exact resolve eq17 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1071
  have eq1425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1405 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1405
    | (have j0 := eq1405 X0 X1
       grind)
    | exact resolve eq1405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1436 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1081 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1081
    | exact resolve eq1081 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1081 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2882 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1413 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1413
    | exact resolve eq1413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq2945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2882 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2882
    | (have j0 := eq2882 X0 X1
       grind)
    | exact resolve eq2882 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882
  have eq7483 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1425 x y
       grind)
    | exact superpose eq1425 eq16
    | (have j1 := eq1425 x y
       grind)
    | exact resolve eq16 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq7586 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq7483
       have i₂ := eq2945 x y
       grind)
    | exact superpose eq2945 eq7483
    | (have j1 := eq2945 x y
       grind)
    | (have r₁ := eq7483
       have r₂ := eq2945 x y
       grind)
    | exact resolve eq7483 eq2945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945 eq7483
  have eq7588 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq7586
  have eq7607 : y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq7588
       have i₂ := eq1081 x y
       grind)
    | exact superpose eq1081 eq7588
    | (have j1 := eq1081 x y
       grind)
    | exact resolve eq7588 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588
  have eq7624 : (σ y) = (σ (M.op y x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq1476 y x
       grind)
    | (have r₁ := eq7607
       have r₂ := eq1476 y x
       grind)
    | exact resolve eq7607 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7607
  have eq7659 : (M.op y x) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq7624
       grind)
    | exact superpose eq7624 eq10
    | exact resolve eq10 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq7712 : y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq7659
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7659
    | exact resolve eq7659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7659
  have eq7714 : y = (k y x) := by
    first
    | (have j1 := eq1476 y x
       grind)
    | (have r₁ := eq7712
       have r₂ := eq1476 y x
       grind)
    | exact resolve eq7712 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq7712
  have eq7724 : x = y ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq616 y x
       have i₂ := eq7714
       grind)
    | exact superpose eq7714 eq616
    | (have j0 := eq616 x y
       grind)
    | exact resolve eq616 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq7979 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7724
       grind)
    | exact superpose eq7724 eq16
    | exact resolve eq16 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7724
  have eq7998 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7979
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq7979
    | exact resolve eq7979 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7979
  have eq7999 : x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq7998
       have r₂ := eq65 (σ x)
       grind)
    | exact resolve eq7998 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7998
  have eq8015 : x = y ∨ x = (k y x) ∨ (k y x) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq431 x y
       have i₂ := eq7999
       grind)
    | exact superpose eq7999 eq431
    | (have j0 := eq431 x y
       grind)
    | exact resolve eq431 eq7999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7999
  have eq8036 : x = y ∨ x = y ∨ (k y x) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8015
       have i₂ := eq7714
       grind)
    | exact superpose eq7714 eq8015
    | exact resolve eq8015 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8015
  have eq8037 : x = y ∨ (k y x) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq8036
  have eq8043 : y = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8037
       have i₂ := eq7714
       grind)
    | exact superpose eq7714 eq8037
    | exact resolve eq8037 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq8044 : x = y ∨ y = (M.op y x) := by grind
  clear eq8043
  have eq8048 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8044
       grind)
    | exact superpose eq8044 eq16
    | exact resolve eq16 eq8044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8069 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8048
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq8048
    | exact resolve eq8048 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8048
  have eq8070 : y = (M.op y x) := by
    first
    | (have r₁ := eq8069
       have r₂ := eq65 (σ x)
       grind)
    | exact resolve eq8069 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069
  have eq8087 : x = y ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq431 y x
       have i₂ := eq8070
       grind)
    | exact superpose eq8070 eq431
    | (have j0 := eq431 y x
       grind)
    | exact resolve eq431 eq8070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8070
  have eq8387 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8087
       grind)
    | exact superpose eq8087 eq16
    | exact resolve eq16 eq8087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8087
  have eq8423 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq8387
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq8387
    | exact resolve eq8387 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8387
  have eq8424 : y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq8423
       have r₂ := eq65 (σ x)
       grind)
    | exact resolve eq8423 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8423
  have eq8440 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1081 y x
       have i₂ := eq8424
       grind)
    | exact superpose eq8424 eq1081
    | (have j0 := eq1081 y x
       grind)
    | exact resolve eq1081 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq8468 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq8424
  have eq8483 : x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq8440
       have r₂ := eq8468
       grind)
    | exact resolve eq8440 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8440 eq8468
  have eq8485 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8483
       grind)
    | exact superpose eq8483 eq16
    | exact resolve eq16 eq8483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8483
  have eq8522 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq8485
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq8485
    | exact resolve eq8485 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8485
  have eq8523 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq8522
       have r₂ := eq65 (σ x)
       grind)
    | exact resolve eq8522 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8522
  have eq9114 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1436 x y
       grind)
    | exact superpose eq1436 eq16
    | (have j1 := eq1436 x y
       grind)
    | exact resolve eq16 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq9184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9114
       have i₂ := eq8523
       grind)
    | exact superpose eq8523 eq9114
    | exact resolve eq9114 eq8523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9114
  have eq9185 : (σ x) = (σ (k x y)) := by grind
  clear eq9184
  have eq9204 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9185
       have i₂ := eq8523
       grind)
    | exact superpose eq8523 eq9185
    | exact resolve eq9185 eq8523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9185
  have eq44248 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq431 X0 X1
       grind)
    | exact superpose eq431 eq629
    | (have j1 := eq431 X1 X0
       grind)
    | exact resolve eq629 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq629
  have eq44416 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44248
  have eq44519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44416 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44416
    | (have j0 := eq44416 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq44416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44416
  have eq53369 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq646
       have i₂ := eq9204
       grind)
    | exact superpose eq9204 eq646
    | exact resolve eq646 eq9204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq53376 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have j1 := eq44519 y x
       grind)
    | (have r₁ := eq53369
       have r₂ := eq44519 x y
       grind)
    | (have r₁ := eq53369
       have r₂ := eq44519 y x
       grind)
    | exact resolve eq53369 eq44519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44519 eq53369
  have eq53383 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq53376
       have i₂ := eq7714
       grind)
    | exact superpose eq7714 eq53376
    | exact resolve eq53376 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53376
  have eq53387 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq53383
       have i₂ := eq7714
       grind)
    | exact superpose eq7714 eq53383
    | exact resolve eq53383 eq7714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7714 eq53383
  have eq53394 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53387
       grind)
    | exact superpose eq53387 eq16
    | exact resolve eq16 eq53387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53387
  have eq53497 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq53394
       have i₂ := eq65 (σ x)
       grind)
    | exact superpose eq65 eq53394
    | exact resolve eq53394 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53394
  have eq53500 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq53497
       have r₂ := eq9204
       grind)
    | exact resolve eq53497 eq9204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53497
  have eq53550 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq412 (σ y) (σ x) x
       have i₂ := eq53500
       grind)
    | exact superpose eq53500 eq412
    | exact resolve eq412 eq53500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq53603 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53550 X0
       have i₂ := eq53500
       grind)
    | exact superpose eq53500 eq53550
    | (have j0 := eq53550 X0
       grind)
    | exact resolve eq53550 eq53500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53500 eq53550
  have eq53632 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq53603 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq53603
    | (have j0 := eq53603 X0
       grind)
    | exact resolve eq53603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53603
  have eq53647 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq53632 X0
       have i₂ := eq8523
       grind)
    | exact superpose eq8523 eq53632
    | (have j0 := eq53632 X0
       grind)
    | exact resolve eq53632 eq8523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8523 eq53632
  have eq53658 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq53647 X0
       grind)
    | (have r₁ := eq53647 X0
       have r₂ := eq16
       grind)
    | exact resolve eq53647 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53647
  have eq56322 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq53658 X0
       grind)
    | exact superpose eq53658 eq16
    | (have j1 := eq53658 X0
       grind)
    | exact resolve eq16 eq53658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53658
  have eq56442 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq56322 X0
       have i₂ := eq65 (σ x)
       grind)
    | exact superpose eq65 eq56322
    | (have j0 := eq56322 X0
       grind)
    | exact resolve eq56322 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq56322
  have eq56443 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq56442 X0
       grind)
    | (have r₁ := eq56442 X0
       have r₂ := eq9204
       grind)
    | exact resolve eq56442 eq9204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56442
  have eq56481 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56443 (M.op (σ y) (M.op x (σ y)))
       have i₂ := eq63 (σ y) x
       grind)
    | exact superpose eq63 eq56443
    | exact resolve eq56443 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq56443
  have eq56632 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56481
       grind)
    | exact superpose eq56481 eq16
    | exact resolve eq16 eq56481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56481
  have eq56737 : False := by grind
  exact eq56737

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pyy_pyy_pyx_Equation1043 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq87 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq71
    | exact resolve eq71 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq87
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq87
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y (M.op y y)
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq14
    | exact resolve eq14 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq489 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq53 X0 X1 X3 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq506
    | exact resolve eq506 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq511 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq503
    | exact resolve eq503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq518 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq508 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq508
    | (have j0 := eq508 y x
       grind)
    | exact resolve eq508 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3902 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq511 X0 X0 x
       grind)
    | exact superpose eq511 eq53
    | exact resolve eq53 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq511
  have eq3935 : y = (M.op y (M.op (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq489 y y
       have i₂ := eq3902 y
       grind)
    | exact superpose eq3902 eq489
    | exact resolve eq489 eq3902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq3902
  have eq21924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq21925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq21924
    | exact resolve eq21924 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21924
  have eq21930 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq21925
       have r₂ := eq28
       grind)
    | exact resolve eq21925 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21925
  have eq21933 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21930 eq112
    | exact resolve eq112 eq21930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq21930
  have eq22013 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq21933
    | exact resolve eq21933 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21933
  have eq22014 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22013
  have eq22025 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq22014
       grind)
    | exact superpose eq22014 eq88
    | exact resolve eq88 eq22014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq22032 : y = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3935
       have i₂ := eq22014
       grind)
    | exact superpose eq22014 eq3935
    | exact resolve eq3935 eq22014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq22036 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq432 y X0
       have i₂ := eq22014
       grind)
    | exact superpose eq22014 eq432
    | exact resolve eq432 eq22014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq22110 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22036 X0
       have i₂ := eq508 (σ y) X0
       grind)
    | exact superpose eq508 eq22036
    | exact resolve eq22036 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq22036
  have eq22113 : y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq518 eq22032
    | exact resolve eq22032 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq22032
  have eq22120 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22025
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22025
    | exact resolve eq22025 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22025
  have eq22129 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22110 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22110
    | (have j0 := eq22110 X0
       grind)
    | exact resolve eq22110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22110
  have eq22341 : x = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22113 eq51
    | exact resolve eq51 eq22113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq22113
  have eq23765 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22129 eq14
    | exact resolve eq14 eq22129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22129
  have eq24238 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22341
       have i₂ := eq22014
       grind)
    | exact superpose eq22014 eq22341
    | exact resolve eq22341 eq22014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22014 eq22341
  have eq24263 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24238
  have eq24272 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24263
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24263
    | exact resolve eq24263 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24263
  have eq24274 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24272 eq30
    | exact resolve eq30 eq24272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24272
  have eq24319 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq24274
    | exact resolve eq24274 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24274
  have eq24320 : x = (M.op x y) ∨ x = y := by grind
  clear eq24319
  have eq24588 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24320 eq21
    | exact resolve eq21 eq24320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24320
  have eq24717 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq24588
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24588
    | exact resolve eq24588 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24588
  have eq24746 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24717 eq27
    | exact resolve eq27 eq24717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24717
  have eq43208 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22120 eq23765
    | exact resolve eq23765 eq22120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22120 eq23765
  have eq43303 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq43208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43208
  have eq43398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43303 eq24746
    | exact resolve eq24746 eq43303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24746 eq43303
  have eq43406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq43398
  have eq43415 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq43406
       have r₂ := eq28
       grind)
    | exact resolve eq43406 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43406
  have eq43434 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq43415 eq30
    | exact resolve eq30 eq43415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43415
  have eq43505 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq43434
    | exact resolve eq43434 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43434
  have eq43506 : x = y := by grind
  clear eq43505
  have eq43515 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq43506
       grind)
    | exact superpose eq43506 eq19
    | exact resolve eq19 eq43506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq43516 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq43506
       grind)
    | exact superpose eq43506 eq25
    | exact resolve eq25 eq43506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq43506
  have eq43646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43516
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43516
    | exact resolve eq43516 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43516
  have eq43677 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43646 eq27
    | exact resolve eq27 eq43646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43646
  have eq43886 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43677 eq78
    | exact resolve eq78 eq43677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq43677
  have eq43951 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq43886
       have i₂ := eq43515
       grind)
    | exact superpose eq43515 eq43886
    | exact resolve eq43886 eq43515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43515 eq43886
  have eq43952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43951 eq15
    | exact resolve eq15 eq43951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43951
  have eq44036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq43952
    | exact resolve eq43952 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43952
  have eq44059 : False := by grind
  exact eq44059

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_pyx_pxy_Equation1043 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq21 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq24 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq52 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq19 X0 X1 X3 X4
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X0 X4)) X4)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X0 X4)) X4))
       have i₂ := eq19 X0 X2 X3 X4
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq24
    | (have j0 := eq24 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X0 X2)) X2))) ∨ (σ (M.op (M.op X1 (M.op X0 X2)) X2)) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X0 X2)) X2))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq24
    | (have j0 := eq24 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
       grind)
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq72 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 (M.op X0 X2)) X2)) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X0 X2)) X2))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X3 (M.op X0 X1)) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X0 X1) X2 X3 X1
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq19
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (M.op X0 (σ X1)) X1
       have i₂ := eq60 (σ X1) X0
       grind)
    | exact superpose eq60 eq29
    | exact resolve eq29 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq60
  have eq364 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 X0 x X0
       have i₂ := eq61 X0 X0 x
       grind)
    | exact superpose eq61 eq19
    | exact resolve eq19 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq442 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1 X0 x X0
       have i₂ := eq61 X0 X0 x
       grind)
    | exact superpose eq61 eq57
    | exact resolve eq57 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq786 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ X1) (M.op (M.op X3 (σ (M.op (M.op X0 (M.op X1 X2)) X2))) (σ (M.op (M.op X0 (M.op X1 X2)) X2)))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 (M.op X1 X2)) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X1) X3 (σ (M.op (M.op X0 (M.op X1 X2)) X2))
       have i₂ := eq72 X1 X0 X2
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X1 X0 X2
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (M.op (M.op X1 (M.op X0 X2)) X2)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ X1) (M.op X3 (σ (M.op (M.op X0 (M.op X1 X2)) X2)))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 (M.op X1 X2)) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq786 X0 X1 X2 X3
       have i₂ := eq59 (σ (M.op (M.op X0 (M.op X1 X2)) X2)) X3
       grind)
    | exact superpose eq59 eq786
    | (have j0 := eq786 X0 X1 X2 X3
       grind)
    | exact resolve eq786 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq16
    | (have j1 := eq63 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq63 x y
       grind)
    | exact resolve eq16 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq993 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq960
  have eq1198 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 X0
       have i₂ := eq364 X0
       grind)
    | exact superpose eq364 eq61
    | exact resolve eq61 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113 (σ x) y
       have i₂ := eq993
       grind)
    | exact superpose eq993 eq113
    | exact resolve eq113 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1431 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1400
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1400
    | exact resolve eq1400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq3647 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113 (σ x) y
       have i₂ := eq1431
       grind)
    | exact superpose eq1431 eq113
    | exact resolve eq113 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq1431
  have eq3683 : y = (k y y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3647
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3647
    | exact resolve eq3647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq5240 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X0 X1 X0
       have i₂ := eq364 X0
       grind)
    | exact superpose eq364 eq91
    | exact resolve eq91 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq364
  have eq5310 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5240 X0 X1
       have i₂ := eq59 (M.op X0 X0) X1
       grind)
    | exact superpose eq59 eq5240
    | exact resolve eq5240 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq6423 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq3683
       grind)
    | exact superpose eq3683 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683
  have eq6424 : x = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6423
  have eq9914 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq6424
       grind)
    | exact superpose eq6424 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq6424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6424
  have eq9915 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq9914
  have eq13555 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 y y x
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq61
    | exact resolve eq61 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13615 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13555 X0
       have i₂ := eq59 y X0
       grind)
    | exact superpose eq59 eq13555
    | exact resolve eq13555 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13555
  have eq13873 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 (M.op X1 X2)) X2))) ∨ (σ X1) = (σ (M.op (M.op X0 (M.op X1 X2)) X2)) ∨ (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 (M.op X1 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq829 X1 X0 X2 (σ X0)
       have i₂ := eq72 X0 X1 X2
       grind)
    | exact superpose eq72 eq829
    | (have j0 := eq829 X0 X1 X2 x
       have j1 := eq72 X1 X0 X2
       grind)
    | exact resolve eq829 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq829
  have eq13992 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 (M.op X1 X2)) X2))) ∨ (σ X1) = (σ (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq13873 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13873
  have eq13993 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 (M.op X1 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq13992 X0 X1 X2
       have j1 := eq808 X1 X0 X2
       grind)
    | (have r₁ := eq13992 X1 X0 X2
       have r₂ := eq808 X0 X1 X2
       grind)
    | exact resolve eq13992 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq13992
  have eq26267 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq13615 X0
       grind)
    | exact superpose eq13615 eq9
    | exact resolve eq9 eq13615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13615
  have eq33358 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26267 X0
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq26267
    | exact resolve eq26267 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9915 eq26267
  have eq33638 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq33358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33358
  have eq40888 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 y x
       have i₂ := eq33638 X0
       grind)
    | exact superpose eq33638 eq59
    | (have j1 := eq33638 y
       grind)
    | exact resolve eq59 eq33638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33638
  have eq61427 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq40888 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40888
  have eq61428 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq61427
  have eq70200 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 y y x
       have i₂ := eq61428
       grind)
    | exact superpose eq61428 eq61
    | exact resolve eq61 eq61428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq70419 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq70200 X0
       have i₂ := eq59 y X0
       grind)
    | exact superpose eq59 eq70200
    | exact resolve eq70200 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq70200
  have eq100509 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq70419 X0
       grind)
    | exact superpose eq70419 eq9
    | exact resolve eq9 eq70419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70419
  have eq114010 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq100509 X0
       have i₂ := eq61428
       grind)
    | exact superpose eq61428 eq100509
    | exact resolve eq100509 eq61428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61428 eq100509
  have eq114504 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq114010 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114010
  have eq128349 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq114504 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114504
  have eq128350 : x = (M.op x y) := by grind
  clear eq128349
  have eq142983 : y = (M.op y (M.op x (M.op y y))) := by
    first
    | (have i₁ := eq442 y x
       have i₂ := eq128350
       grind)
    | exact superpose eq128350 eq442
    | exact resolve eq442 eq128350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq229853 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq5310 X0 X1
       grind)
    | exact superpose eq5310 eq9
    | exact resolve eq9 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310
  have eq230930 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq229853 X0 X1
       have i₂ := eq1198 X0
       grind)
    | exact superpose eq1198 eq229853
    | exact resolve eq229853 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq229853
  have eq242137 : (σ x) = (M.op (σ x) (σ (M.op y (M.op y y)))) := by
    first
    | (have i₁ := eq13993 y x (M.op y y)
       have i₂ := eq142983
       grind)
    | exact superpose eq142983 eq13993
    | exact resolve eq13993 eq142983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13993 eq142983
  have eq242680 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq242137
       have i₂ := eq230930 y y
       grind)
    | exact superpose eq230930 eq242137
    | exact resolve eq242137 eq230930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230930 eq242137
  have eq291690 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq242680
       grind)
    | exact superpose eq242680 eq16
    | exact resolve eq16 eq242680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242680
  have eq292036 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq291690
       have i₂ := eq128350
       grind)
    | exact superpose eq128350 eq291690
    | exact resolve eq291690 eq128350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128350 eq291690
  have eq292037 : False := by grind
  exact eq292037

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_pxy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have i₂ := eq54 X1 X2 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have r₂ := eq54 X0 X1 X2
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq379 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq398 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X0 X1
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
  have eq408 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq14 X0 X1
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
  have eq409 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X2) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq408 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq502 : ∀ X0 X1 X2 : G, (k (τ (M.op X2 (M.op X0 (M.op X2 X0)))) X1) = (τ (M.op (M.op X2 (M.op X0 (M.op X2 X0))) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op X2 (M.op X0 (M.op X2 X0))) X1
       have i₂ := eq65 (σ X1) X2 X0
       grind)
    | exact superpose eq65 eq22
    | exact resolve eq22 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq503 : ∀ X0 X1 X2 : G, (k (σ (M.op X2 (M.op X0 (M.op X2 X0)))) X1) = (σ (M.op (M.op X2 (M.op X0 (M.op X2 X0))) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 (M.op X2 (M.op X0 (M.op X2 X0)))
       have i₂ := eq65 (τ X1) X2 X0
       grind)
    | exact superpose eq65 eq18
    | exact resolve eq18 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2289 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq2290 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq2319 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2290 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2321 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2319 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2319
    | (have j0 := eq2319 (σ X0)
       grind)
    | exact resolve eq2319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2371 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2321 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2387 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2371 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq2371
    | (have j0 := eq2371 (τ X0)
       grind)
    | exact resolve eq2371 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2394 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2387 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq2387
    | (have j0 := eq2387 X0
       grind)
    | exact resolve eq2387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2401 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2394 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2394
    | (have j0 := eq2394 X0
       grind)
    | exact resolve eq2394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2402 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2401 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2401
    | (have j0 := eq2401 X0
       grind)
    | exact resolve eq2401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2412 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2402 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq2402
    | (have j0 := eq2402 (τ X0)
       grind)
    | exact resolve eq2402 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq2424 : ∀ X0 X1 : G, (τ X1) ≠ (τ X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2412 X1
       have i₂ := eq410 X0 X1
       grind)
    | exact superpose eq410 eq2412
    | (have j0 := eq2412 X1
       have j1 := eq410 X0 X1
       grind)
    | exact resolve eq2412 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq2412
  have eq2431 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq3056 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq3851 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2431 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2431
    | (have j0 := eq2431 X1 (σ X0)
       grind)
    | exact resolve eq2431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431
  have eq4279 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq398 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq398
    | (have j0 := eq398 X0 X1
       grind)
    | exact resolve eq398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq4348 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4279 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4279
    | (have j0 := eq4279 X1 X1
       grind)
    | exact resolve eq4279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq8324 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3851 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3851
    | (have j0 := eq3851 X1 (σ X0)
       grind)
    | exact resolve eq3851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq19332 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X1 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3056 (τ X0) (τ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq3056
    | (have j0 := eq3056 (τ X0) (τ X0)
       grind)
    | exact resolve eq3056 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq19421 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19332 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq19332
    | (have j0 := eq19332 X0 X0
       grind)
    | exact resolve eq19332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19332
  have eq19443 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19421 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19421
    | (have j0 := eq19421 X0 X0
       grind)
    | exact resolve eq19421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19421
  have eq19461 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19443 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19443
    | (have j0 := eq19443 X0 X1
       grind)
    | exact resolve eq19443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19443
  have eq19478 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19461 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19461
    | (have j0 := eq19461 X0 X1
       grind)
    | exact resolve eq19461 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19461
  have eq19491 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19478 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19478
    | (have j0 := eq19478 X0 X1
       grind)
    | exact resolve eq19478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19478
  have eq19554 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19491 (τ X0) (τ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq19491
    | (have j0 := eq19491 (τ X0) (τ X0)
       grind)
    | exact resolve eq19491 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq68729 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8324 y x
       grind)
    | exact superpose eq8324 eq16
    | (have j1 := eq8324 y x
       grind)
    | exact resolve eq16 eq8324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324
  have eq69768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68729
       have i₂ := eq4348 y x
       grind)
    | exact superpose eq4348 eq68729
    | (have j1 := eq4348 x x
       grind)
    | (have r₁ := eq68729
       have r₂ := eq4348 y x
       grind)
    | exact resolve eq68729 eq4348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4348 eq68729
  have eq69778 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq69768
  have eq69779 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq69778
  have eq69794 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54 (σ x) (σ y) X0
       have i₂ := eq69779
       grind)
    | exact superpose eq69779 eq54
    | exact resolve eq54 eq69779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69779
  have eq72211 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54 (σ y) (σ x) X0
       have i₂ := eq69794 (σ y)
       grind)
    | exact superpose eq69794 eq54
    | exact resolve eq54 eq69794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72227 : ∀ X0 : G, (τ (M.op (σ y) (σ X0))) = (k (τ (σ y)) X0) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq502 (σ x) x (σ y)
       have i₂ := eq69794 (σ y)
       grind)
    | exact superpose eq69794 eq502
    | exact resolve eq502 eq69794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq69794
  have eq72515 : ∀ X0 : G, (τ (M.op (σ y) (σ X0))) = (k y X0) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq72227 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq72227
    | exact resolve eq72227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72227
  have eq74187 : (τ (σ y)) = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72515 y
       have i₂ := eq72211 (σ y)
       grind)
    | exact superpose eq72211 eq72515
    | exact resolve eq72515 eq72211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72211 eq72515
  have eq74311 : (τ (σ y)) = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq74187
  have eq74319 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74311
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq74311
    | exact resolve eq74311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74311
  have eq74378 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19491 y y
       have i₂ := eq74319
       grind)
    | exact superpose eq74319 eq19491
    | (have j0 := eq19491 y y
       grind)
    | (have r₁ := eq19491 y y
       have r₂ := eq74319
       grind)
    | exact resolve eq19491 eq74319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19491 eq74319
  have eq74410 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq74378
  have eq74411 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq74410
  have eq74902 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq74411
       grind)
    | exact superpose eq74411 eq9
    | exact resolve eq9 eq74411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75217 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74902 X0
       have i₂ := eq74411
       grind)
    | exact superpose eq74411 eq74902
    | exact resolve eq74902 eq74411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74902
  have eq75480 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq75217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75217
  have eq75516 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq75480 X0
       have i₂ := eq74411
       grind)
    | exact superpose eq74411 eq75480
    | exact resolve eq75480 eq74411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74411 eq75480
  have eq75779 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq75516 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75516
  have eq76078 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq75779 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75779
  have eq76079 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq76078
  have eq76095 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq76079
       grind)
    | exact superpose eq76079 eq54
    | exact resolve eq54 eq76079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76079
  have eq76543 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq54 y x X0
       have i₂ := eq76095 y
       grind)
    | exact superpose eq76095 eq54
    | exact resolve eq54 eq76095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76095
  have eq77083 : ∀ X0 : G, x ≠ x ∨ x = (k x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq76543 X0
       grind)
    | exact superpose eq76543 eq12
    | (have j1 := eq76543 X0
       grind)
    | (have r₁ := eq12 y X0
       have r₂ := eq76543 X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq76543 X0
       grind)
    | exact resolve eq12 eq76543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77085 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 x x X0
       have i₂ := eq76543 X1
       grind)
    | exact superpose eq76543 eq54
    | (have j1 := eq76543 X1
       grind)
    | exact resolve eq54 eq76543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76543
  have eq77129 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq77083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77083
  have eq77231 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19554 x x
       have i₂ := eq77129 X0
       grind)
    | exact superpose eq77129 eq19554
    | (have j0 := eq19554 x x
       have j1 := eq77129 X0
       grind)
    | exact resolve eq19554 eq77129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19554 eq77129
  have eq77462 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq77231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77231
  have eq77463 : ∀ X0 : G, (τ x) = (M.op (τ x) (τ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq77462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77462
  have eq78750 : ∀ X0 X1 : G, (M.op X0 (M.op (τ x) (M.op (τ x) (τ x)))) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (τ x) (τ x) X0
       have i₂ := eq77463 X1
       grind)
    | exact superpose eq77463 eq54
    | (have j1 := eq77463 X1
       grind)
    | exact resolve eq54 eq77463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77463
  have eq81968 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 x x X0
       have i₂ := eq77085 x X1
       grind)
    | exact superpose eq77085 eq54
    | (have j1 := eq77085 X0 X1
       grind)
    | exact resolve eq54 eq77085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81971 : ∀ X0 X1 : G, (M.op x X0) = (k x X0) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 x x
       have i₂ := eq77085 x X1
       grind)
    | exact superpose eq77085 eq65
    | (have j1 := eq77085 X0 X1
       grind)
    | exact resolve eq65 eq77085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81986 : ∀ X0 X1 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq503 x X1 x
       have i₂ := eq77085 x X1
       grind)
    | exact superpose eq77085 eq503
    | (have j1 := eq77085 X0 X1
       grind)
    | exact resolve eq503 eq77085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq77085
  have eq94302 : ∀ X0 X1 : G, (σ (M.op x X0)) = (k (σ x) (σ X0)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81986 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81986
    | (have j0 := eq81986 X0 X1
       grind)
    | exact resolve eq81986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81986
  have eq94669 : ∀ X0 X1 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94302 X0 X1
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq94302
    | (have j0 := eq94302 X0 X1
       grind)
    | exact resolve eq94302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94302
  have eq142000 : ∀ X0 X1 : G, (k (τ x) X0) = (M.op (τ x) X0) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (τ x) (τ x)
       have i₂ := eq78750 (τ x) X1
       grind)
    | exact superpose eq78750 eq65
    | (have j1 := eq78750 X0 X1
       grind)
    | exact resolve eq65 eq78750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78750
  have eq143754 : ∀ X0 X1 : G, (k x (σ X0)) = (σ (M.op (τ x) X0)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 x X0
       have i₂ := eq142000 X0 X1
       grind)
    | exact superpose eq142000 eq17
    | (have j1 := eq142000 X0 X1
       grind)
    | exact resolve eq17 eq142000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq142000
  have eq148838 : ∀ X0 X1 : G, (σ (τ x)) = (k x (σ x)) ∨ (M.op X0 y) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143754 x X0
       have i₂ := eq81968 (τ x) X1
       grind)
    | exact superpose eq81968 eq143754
    | (have j0 := eq143754 X0 X0
       have j1 := eq81968 X0 X0
       grind)
    | exact resolve eq143754 eq81968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81968 eq143754
  have eq149214 : ∀ X0 X1 : G, x = (k x (σ x)) ∨ (M.op X0 y) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148838 X0 X1
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq148838
    | (have j0 := eq148838 X0 X0
       grind)
    | exact resolve eq148838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148838
  have eq153859 : ∀ X0 : G, X0 ≠ X0 ∨ x = (k x (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq149214 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149214
  have eq153860 : ∀ X0 : G, x = (k x (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq153859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153859
  have eq153876 : ∀ X0 X1 : G, x = (M.op x (σ x)) ∨ (M.op X0 y) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81971 (σ x) X0
       have i₂ := eq153860 X1
       grind)
    | exact superpose eq153860 eq81971
    | (have j0 := eq81971 X0 X0
       have j1 := eq153860 X0
       grind)
    | exact resolve eq81971 eq153860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81971 eq153860
  have eq157415 : ∀ X0 : G, X0 ≠ X0 ∨ x = (M.op x (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq153876 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153876
  have eq157416 : ∀ X0 : G, x = (M.op x (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq157415 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157415
  have eq158208 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (σ x) x))) = X0 ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 x (σ x) X0
       have i₂ := eq157416 X1
       grind)
    | exact superpose eq157416 eq54
    | (have j1 := eq157416 X1
       grind)
    | exact resolve eq54 eq157416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157416
  have eq159749 : ∀ X0 X1 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (σ x) x
       have i₂ := eq158208 (σ x) X1
       grind)
    | exact superpose eq158208 eq65
    | (have j1 := eq158208 X0 X1
       grind)
    | exact resolve eq65 eq158208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq158208
  have eq161517 : ∀ X0 X1 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq159749 (σ X0) X1
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq159749
    | (have j0 := eq159749 X0 X1
       grind)
    | exact resolve eq159749 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159749
  have eq169635 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq161517 y X0
       grind)
    | exact superpose eq161517 eq16
    | (have j1 := eq161517 X0 X0
       grind)
    | exact resolve eq16 eq161517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161517
  have eq170035 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X1 y) = X1 ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169635 X1
       have i₂ := eq94669 y X0
       grind)
    | exact superpose eq94669 eq169635
    | (have j0 := eq169635 X1
       have j1 := eq94669 X0 X1
       grind)
    | (have r₁ := eq169635 X0
       have r₂ := eq94669 y X1
       grind)
    | exact resolve eq169635 eq94669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94669 eq169635
  have eq170043 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq170035 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170035
  have eq170686 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq170043 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170043
  have eq170687 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq170686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170686
  have eq170711 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq170687 X0
       grind)
    | exact superpose eq170687 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y X0
       have r₂ := eq170687 X0
       grind)
    | exact resolve eq12 eq170687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170924 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq170711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170711
  have eq171070 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2371 y
       have i₂ := eq170924 y
       grind)
    | exact superpose eq170924 eq2371
    | (have j0 := eq2371 y
       grind)
    | exact resolve eq2371 eq170924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371 eq170924
  have eq171276 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq171070
       have i₂ := eq170687 y
       grind)
    | exact superpose eq170687 eq171070
    | exact resolve eq171070 eq170687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171070
  have eq171277 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq171276
  have eq171799 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 (σ y) (σ y) X0
       have i₂ := eq171277
       grind)
    | exact superpose eq171277 eq54
    | exact resolve eq54 eq171277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq171888 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq171799 X0
       have i₂ := eq171277
       grind)
    | exact superpose eq171277 eq171799
    | exact resolve eq171799 eq171277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171799
  have eq171936 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq171888 X0
       have i₂ := eq171277
       grind)
    | exact superpose eq171277 eq171888
    | exact resolve eq171888 eq171277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171277 eq171888
  have eq172127 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171936 (σ x)
       grind)
    | exact superpose eq171936 eq16
    | exact resolve eq16 eq171936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171936
  have eq172160 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq172127
       have i₂ := eq170687 x
       grind)
    | exact superpose eq170687 eq172127
    | exact resolve eq172127 eq170687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170687 eq172127
  have eq172161 : False := by grind
  exact eq172161

/-- `Equation1230`: `x = x ◇ (((x ◇ y) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation1230 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1230 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1230.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq50
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq98 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq658 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 (τ X0) (τ X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq105
    | (have j0 := eq105 (τ X0) (τ X1)
       grind)
    | exact resolve eq105 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq669 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq666
    | (have j0 := eq666 X0 X1
       grind)
    | exact resolve eq666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq671 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq672 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq673 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq672
    | (have j0 := eq672 X0 X1
       grind)
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq674 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq673 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq673
    | (have j0 := eq673 X0 X1
       grind)
    | exact resolve eq673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq3882 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq71 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq71 X0 (σ X0)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3893 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq3894 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq3895 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3882 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq3896 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3895 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq3899 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3894 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3894
    | (have j0 := eq3894 X0
       grind)
    | exact resolve eq3894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894
  have eq3983 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq3899 X0
       grind)
    | exact superpose eq3899 eq57
    | (have j1 := eq3899 X0
       grind)
    | exact resolve eq57 eq3899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq3899
  have eq3995 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3983 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3983
    | (have j0 := eq3983 X0
       grind)
    | exact resolve eq3983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq3996 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq3998 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3996 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3996
    | exact resolve eq3996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4022 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3996 X0
       grind)
    | exact superpose eq3996 eq11
    | exact resolve eq11 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4071 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3998 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq3998
    | exact resolve eq3998 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3998
  have eq4104 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4071 X0
       grind)
    | exact superpose eq4071 eq11
    | exact resolve eq11 eq4071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4191 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4104 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4104
    | exact resolve eq4104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4258 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq4191 (τ X0)
       grind)
    | exact superpose eq4191 eq53
    | exact resolve eq53 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4310 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4258 X0
       have i₂ := eq4071 X0
       grind)
    | exact superpose eq4071 eq4258
    | exact resolve eq4258 eq4071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071 eq4258
  have eq4859 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4875 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4859 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4859
    | exact resolve eq4859 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4907 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4875 X0
       have i₂ := eq4191 X0
       grind)
    | exact superpose eq4191 eq4875
    | exact resolve eq4875 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4875
  have eq4924 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4907
  have eq51123 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3896 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3896
    | exact resolve eq3896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51227 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X1) X0
       have i₂ := eq3896 (σ X0) X1
       grind)
    | exact superpose eq3896 eq39
    | (have j1 := eq3896 (σ X0) X1
       grind)
    | exact resolve eq39 eq3896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq51340 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51227 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq51227
    | (have j0 := eq51227 X0 X1
       grind)
    | exact resolve eq51227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51227
  have eq51400 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq51123 X0 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51123
    | (have j0 := eq51123 X0 X1
       grind)
    | exact resolve eq51123 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51123
  have eq51434 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51340 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51340
    | (have j0 := eq51340 X0 X1
       grind)
    | exact resolve eq51340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51340
  have eq51516 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51434 X0 X1
       have i₂ := eq4022 X0
       grind)
    | exact superpose eq4022 eq51434
    | (have j0 := eq51434 X0 X1
       grind)
    | exact resolve eq51434 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51434
  have eq51571 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51516 X0 X1
       have i₂ := eq4191 X0
       grind)
    | exact superpose eq4191 eq51516
    | (have j0 := eq51516 X0 X1
       grind)
    | exact resolve eq51516 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51516
  have eq51615 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51571 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51571
    | (have j0 := eq51571 X0 X1
       grind)
    | exact resolve eq51571 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51571
  have eq52803 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq51400 X0 X1
       grind)
    | exact superpose eq51400 eq11
    | (have j1 := eq51400 X0 X1
       grind)
    | exact resolve eq11 eq51400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51400
  have eq53014 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52803 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq52803
    | (have j0 := eq52803 X0 X1
       grind)
    | exact resolve eq52803 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52803
  have eq53340 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq53014 (τ X0) X1
       grind)
    | exact superpose eq53014 eq18
    | (have j1 := eq53014 (τ X0) X1
       grind)
    | exact resolve eq18 eq53014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq53014
  have eq58481 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51615 (τ X0) (τ X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq51615
    | (have j0 := eq51615 (τ X1) (τ X0)
       grind)
    | exact resolve eq51615 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq51615
  have eq58879 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58481 X0 X1
       have i₂ := eq4310 X1
       grind)
    | exact superpose eq4310 eq58481
    | (have j0 := eq58481 X0 X1
       grind)
    | exact resolve eq58481 eq4310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58481
  have eq59037 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58879 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq58879
    | (have j0 := eq58879 X0 X1
       grind)
    | exact resolve eq58879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58879
  have eq59169 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq59037 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59037
    | (have j0 := eq59037 X0 X1
       grind)
    | exact resolve eq59037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59037
  have eq59280 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59169 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq59169
    | (have j0 := eq59169 X0 X1
       grind)
    | exact resolve eq59169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59169
  have eq59363 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59280 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59280
    | (have j0 := eq59280 X0 X1
       grind)
    | exact resolve eq59280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59280
  have eq60793 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq59363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59363
  have eq64962 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq53340 X1 (τ X0)
       grind)
    | exact superpose eq53340 eq19
    | (have j1 := eq53340 X1 (τ X0)
       grind)
    | exact resolve eq19 eq53340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq53340
  have eq65063 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64962 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq64962
    | (have j0 := eq64962 X0 X1
       grind)
    | exact resolve eq64962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64962
  have eq65176 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65063 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65063
    | (have j0 := eq65063 X0 X1
       grind)
    | exact resolve eq65063 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65063
  have eq65264 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65176 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65176
    | (have j0 := eq65176 X0 X1
       grind)
    | exact resolve eq65176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65176
  have eq65346 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65264 X0 X1
       have i₂ := eq4310 X0
       grind)
    | exact superpose eq4310 eq65264
    | (have j0 := eq65264 X0 X1
       grind)
    | exact resolve eq65264 eq4310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4310 eq65264
  have eq70586 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ (M.op X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq65346 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65346
    | (have j0 := eq65346 X1 (σ X0)
       grind)
    | exact resolve eq65346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65346
  have eq72819 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq70586 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq70586
    | (have j0 := eq70586 X0 (σ X1)
       grind)
    | exact resolve eq70586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70586
  have eq73060 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq72819 X0 X1
       have i₂ := eq3996 X1
       grind)
    | exact superpose eq3996 eq72819
    | (have j0 := eq72819 X0 X1
       grind)
    | exact resolve eq72819 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996 eq72819
  have eq73172 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq73060 X0 X1
       have i₂ := eq4191 X1
       grind)
    | exact superpose eq4191 eq73060
    | (have j0 := eq73060 X0 X1
       grind)
    | exact resolve eq73060 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73060
  have eq73260 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73172 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq73172
    | (have j0 := eq73172 X0 X1
       grind)
    | exact resolve eq73172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73172
  have eq75241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq73260 x y
       grind)
    | exact superpose eq73260 eq98
    | (have j1 := eq73260 x y
       grind)
    | (have r₁ := eq98
       have r₂ := eq73260 x y
       grind)
    | exact resolve eq98 eq73260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq73260
  have eq75371 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq75241
  have eq75439 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq105 x y
       grind)
    | (have r₁ := eq75371
       have r₂ := eq105 x y
       grind)
    | exact resolve eq75371 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq75371
  have eq75583 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75439
       have i₂ := eq4022 y
       grind)
    | exact superpose eq4022 eq75439
    | exact resolve eq75439 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75439
  have eq75678 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75583
       have i₂ := eq4191 y
       grind)
    | exact superpose eq4191 eq75583
    | exact resolve eq75583 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75583
  have eq78847 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75678
       grind)
    | exact superpose eq75678 eq16
    | exact resolve eq16 eq75678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78855 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq60793 (σ x) (σ y)
       have i₂ := eq75678
       grind)
    | exact superpose eq75678 eq60793
    | (have j0 := eq60793 (σ x) (σ y)
       grind)
    | exact resolve eq60793 eq75678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60793 eq75678
  have eq78858 : (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq78855
  have eq78863 : (σ x) = (σ (k y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78858
       have i₂ := eq4022 y
       grind)
    | exact superpose eq4022 eq78858
    | exact resolve eq78858 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022 eq78858
  have eq78869 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78863
       have i₂ := eq4191 y
       grind)
    | exact superpose eq4191 eq78863
    | exact resolve eq78863 eq4191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191 eq78863
  have eq78870 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq78869
  have eq78873 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78870
       have i₂ := eq39 (σ x) y
       grind)
    | exact superpose eq39 eq78870
    | exact resolve eq78870 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq78870
  have eq78874 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78873
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78873
    | exact resolve eq78873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78873
  have eq78875 : y = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78874
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq78874
    | exact resolve eq78874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78874
  have eq79874 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq674 x y
       have i₂ := eq78875
       grind)
    | exact superpose eq78875 eq674
    | (have j0 := eq674 x y
       grind)
    | (have r₁ := eq674 x y
       have r₂ := eq78875
       grind)
    | exact resolve eq674 eq78875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq78875
  have eq79886 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq79874
  have eq79887 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq79886
  have eq80548 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq78847
       have i₂ := eq79887
       grind)
    | exact superpose eq79887 eq78847
    | exact resolve eq78847 eq79887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78847 eq79887
  have eq80552 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq80548
  have eq80553 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq80552
  have eq80577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4924 y
       have i₂ := eq80553
       grind)
    | exact superpose eq80553 eq4924
    | exact resolve eq4924 eq80553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80553
  have eq80644 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq80577
       have r₂ := eq16
       grind)
    | exact resolve eq80577 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80577
  have eq81337 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq80644
       grind)
    | exact superpose eq80644 eq10
    | exact resolve eq10 eq80644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80644
  have eq81533 : x = (M.op y y) := by
    first
    | (have i₁ := eq81337
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq81337
    | exact resolve eq81337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81337
  have eq81674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4924 y
       have i₂ := eq81533
       grind)
    | exact superpose eq81533 eq4924
    | exact resolve eq4924 eq81533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924 eq81533
  have eq81743 : False := by grind
  exact eq81743

/-- `Equation1250`: `x = x ◇ (((y ◇ y) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1250 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1250 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1250.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq120 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq260 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq261 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq266 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       have j1 := eq120 X0 X1
       grind)
    | (have r₁ := eq261 X0 X1
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq261 X1 X1
       have r₂ := eq120 X1 X1
       grind)
    | exact resolve eq261 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq261
  have eq291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq266 (σ X0) (σ X1)
       grind)
    | exact superpose eq266 eq15
    | exact resolve eq15 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq291
    | exact resolve eq291 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq291
  have eq298 : False := by grind
  exact eq298

/-- `Equation1255`: `x = x ◇ (((y ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxy_pxx_pxy_Equation1255 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq64 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq65 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq65 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq76 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq66 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq70
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq76 X0 X1
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq76 X1 X0
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq76 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq76
  have eq324 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq329 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq324 X0 X1
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq324 X0 X1
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq324 X1 X1
       have r₂ := eq89 X1 X1
       grind)
    | exact resolve eq324 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq324
  have eq406 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq329 (σ X0) (σ X1)
       grind)
    | exact superpose eq329 eq15
    | exact resolve eq15 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq329 X0 X1
       grind)
    | exact superpose eq329 eq406
    | exact resolve eq406 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq406
  have eq414 : False := by grind
  exact eq414

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxx_x_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq32 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y X0 x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) X0 (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq82 : ∀ X1 : G, (M.op x y) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq111
    | exact resolve eq111 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq111
  have eq173 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq112 (M.op X0 (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq112
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq328 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq82 eq54
    | exact resolve eq54 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq334 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq89 eq54
    | exact resolve eq54 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq399 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq67
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq400 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq399
    | exact resolve eq399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq404 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq400
    | exact resolve eq400 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq6906 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq328 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq328 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq328 eq9
    | exact resolve eq9 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6922 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq53 sF0
       have i₂ := eq328 sF0 x sF0
       grind)
    | (have i₁ := eq53 X0
       have i₂ := eq328 X0 x sF0
       grind)
    | exact superpose eq328 eq53
    | exact resolve eq53 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6927 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq89 sF2
       have i₂ := eq328 sF2 sF4 sF2
       grind)
    | (have i₁ := eq89 X0
       have i₂ := eq328 X0 sF4 sF2
       grind)
    | exact superpose eq328 eq89
    | exact resolve eq89 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq6933 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq59 sF4
       have i₂ := eq328 sF4 sF2 sF4
       grind)
    | (have i₁ := eq59 X0
       have i₂ := eq328 X0 sF2 sF4
       grind)
    | exact superpose eq328 eq59
    | exact resolve eq59 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq9301 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq6906 X0 x X1
       grind)
    | exact superpose eq6906 eq9
    | exact resolve eq9 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq42818 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9301 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))) x
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq9301
    | exact resolve eq9301 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq42973 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq42818 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42818
    | (have j0 := eq42818 x X0
       grind)
    | exact resolve eq42818 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42818
  have eq43303 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x (M.op x x)))) := by
    first
    | exact superpose eq6927 eq42973
    | (have j0 := eq42973 (σ y)
       grind)
    | exact resolve eq42973 eq6927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42973
  have eq44564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq404
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq404
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq404 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq44607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44564
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44564
    | exact resolve eq44564 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44564
  have eq44610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq44607
    | exact resolve eq44607 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44607
  have eq44611 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq44610
       have r₂ := eq28
       grind)
    | exact resolve eq44610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44610
  have eq44612 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44611
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44611
    | exact resolve eq44611 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44611
  have eq44613 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44612 eq58
    | exact resolve eq58 eq44612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq44631 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44612 eq6933
    | exact resolve eq6933 eq44612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933 eq44612
  have eq44686 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq334 eq44631
    | exact resolve eq44631 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq44631
  have eq46001 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44686 eq44613
    | exact resolve eq44613 eq44686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44613 eq44686
  have eq46059 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq46001
  have eq46111 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq46059 eq220
    | exact resolve eq220 eq46059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq46059
  have eq46166 : (τ (σ y)) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39 eq46111
    | exact resolve eq46111 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46111
  have eq46189 : y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq46166
    | exact resolve eq46166 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46166
  have eq46190 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq46189
  have eq46194 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq46190
       grind)
    | exact superpose eq46190 eq55
    | exact resolve eq55 eq46190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq46211 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6922 y
       have i₂ := eq46190
       grind)
    | exact superpose eq46190 eq6922
    | exact resolve eq6922 eq46190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922 eq46190
  have eq46265 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq332 eq46211
    | exact resolve eq46211 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq46211
  have eq47039 : x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq46265 eq46194
    | exact resolve eq46194 eq46265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46194 eq46265
  have eq47099 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq47039
  have eq48459 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43303
       have i₂ := eq47099
       grind)
    | exact superpose eq47099 eq43303
    | exact resolve eq43303 eq47099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43303
  have eq48486 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq47099
       grind)
    | exact superpose eq47099 eq112
    | exact resolve eq112 eq47099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48487 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq173 x
       have i₂ := eq47099
       grind)
    | exact superpose eq47099 eq173
    | exact resolve eq173 eq47099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq47099
  have eq48544 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48487
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48487
    | exact resolve eq48487 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48487
  have eq48545 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48486
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48486
    | exact resolve eq48486 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48486
  have eq48555 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48459
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48459
    | exact resolve eq48459 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48459
  have eq48561 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48544
    | exact resolve eq48544 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48544
  have eq48562 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48545
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq48545
    | exact resolve eq48545 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48545
  have eq48566 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48555
    | exact resolve eq48555 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48555
  have eq48569 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48561
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48561
    | exact resolve eq48561 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48561
  have eq48682 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48562 eq59
    | exact resolve eq59 eq48562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq48562
  have eq48771 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48682
    | exact resolve eq48682 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48682
  have eq48798 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq48566 eq9
    | exact resolve eq9 eq48566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48566
  have eq48919 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48771 eq6927
    | exact resolve eq6927 eq48771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927 eq48771
  have eq58451 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48569 eq48798
    | exact resolve eq48798 eq48569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48569 eq48798
  have eq58633 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58451
  have eq58644 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq335 eq58633
    | exact resolve eq58633 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq58633
  have eq58650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq58644 eq48919
    | exact resolve eq48919 eq58644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48919 eq58644
  have eq58718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58650
  have eq58732 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq58718
       have r₂ := eq28
       grind)
    | exact resolve eq58718 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58718
  have eq58739 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq58732 eq40
    | exact resolve eq40 eq58732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq58732
  have eq58805 : x = y ∨ x = y := by
    first
    | exact superpose eq39 eq58739
    | exact resolve eq58739 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq58739
  have eq58806 : x = y := by grind
  clear eq58805
  have eq58810 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq58806
       grind)
    | exact superpose eq58806 eq19
    | exact resolve eq19 eq58806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq58811 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq58806
       grind)
    | exact superpose eq58806 eq25
    | exact resolve eq25 eq58806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq58806
  have eq61801 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq58811
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq58811
    | exact resolve eq58811 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58811
  have eq62663 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq61801 eq27
    | exact resolve eq27 eq61801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq61801
  have eq65599 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq58810
       grind)
    | exact superpose eq58810 eq112
    | exact resolve eq112 eq58810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq58810
  have eq66011 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65599
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65599
    | exact resolve eq65599 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq65599
  have eq66369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62663 eq66011
    | exact resolve eq66011 eq62663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62663 eq66011
  have eq66597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq66369
    | exact resolve eq66369 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq66369
  have eq66759 : False := by grind
  exact eq66759
