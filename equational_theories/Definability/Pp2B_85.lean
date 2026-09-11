import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq315 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X1
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
  have eq321 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq322 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq321 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq344 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq322 X0 X1
       grind)
    | exact superpose eq322 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq322 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq322 X0 X1
       grind)
    | exact resolve eq12 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq381 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq344 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq397 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
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
  have eq424 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op X3 (M.op X3 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq397 x X2 X3
       have i₂ := eq397 x X2 X0
       grind)
    | exact superpose eq397 eq397
    | exact resolve eq397 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq397 x X2 X0
       grind)
    | exact superpose eq397 eq9
    | exact resolve eq9 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq466 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq431 X0 (M.op X0 X0)
       have i₂ := eq431 X0 X0
       grind)
    | exact superpose eq431 eq431
    | exact resolve eq431 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X0 (M.op X0 X2)) X2
       have i₂ := eq431 X0 X2
       grind)
    | exact superpose eq431 eq54
    | exact resolve eq54 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq477 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq472 X2 X0 X2
       have i₂ := eq431 X0 X2
       grind)
    | (have i₁ := eq472 X0 X1 X2
       have i₂ := eq431 X0 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq431 eq472
    | exact resolve eq472 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq489 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq466 X0
       grind)
    | exact superpose eq466 eq9
    | exact resolve eq9 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq431 (M.op X0 X0) X0
       have i₂ := eq466 X0
       grind)
    | exact superpose eq466 eq431
    | exact resolve eq431 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq466
  have eq552 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq424 X2 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq489 X0 X1
       grind)
    | exact superpose eq489 eq424
    | exact resolve eq424 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq762 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq489 X0 X1
       grind)
    | exact superpose eq489 eq477
    | exact resolve eq477 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq799 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1 x
       have i₂ := eq552 X0 X1 x
       grind)
    | exact superpose eq552 eq762
    | exact resolve eq762 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq762
  have eq920 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq799 (M.op X0 X1) X0
       have i₂ := eq477 X1 X0 X0
       grind)
    | exact superpose eq477 eq799
    | exact resolve eq799 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq799
  have eq1154 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq920 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq920 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq920
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq920 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1179 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X0 X1
       have i₂ := eq496 X1
       grind)
    | exact superpose eq496 eq1154
    | (have j0 := eq1154 X0 X1
       grind)
    | exact resolve eq1154 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq1154
  have eq12744 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq1179 X0 X1
       grind)
    | exact superpose eq1179 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq1179 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1179 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1179 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq1179 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq12761 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X2) = (k X2 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq12744 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq66516 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12761 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12761
  have eq66517 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66516 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66516
  have eq66521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66517 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq66517
    | (have j0 := eq66517 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq66517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66532 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq66517 X0 (τ X1)
       grind)
    | exact superpose eq66517 eq18
    | (have j1 := eq66517 (k (σ X0) X1) (σ (M.op (τ X1) X0))
       grind)
    | exact resolve eq18 eq66517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq66517
  have eq66678 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66532 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66532
    | exact resolve eq66532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66532
  have eq66805 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66678 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq66678
    | (have j0 := eq66678 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq66678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66678
  have eq67384 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66521 y x
       grind)
    | exact superpose eq66521 eq16
    | (have j1 := eq66521 x y
       grind)
    | exact resolve eq16 eq66521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66521
  have eq67547 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67384
       have i₂ := eq66805 x y
       grind)
    | exact superpose eq66805 eq67384
    | (have j1 := eq66805 (σ x) (σ y)
       grind)
    | (have r₁ := eq67384
       have r₂ := eq66805 x y
       grind)
    | (have r₁ := eq67384
       have r₂ := eq66805 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq67384
       have r₂ := eq66805 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq67384 eq66805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66805 eq67384
  have eq67548 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq67547
  have eq67558 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67548
       grind)
    | exact superpose eq67548 eq10
    | exact resolve eq10 eq67548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67548
  have eq67600 : x = y ∨ x = y := by
    first
    | (have i₁ := eq67558
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq67558
    | exact resolve eq67558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67558
  have eq67601 : x = y := by grind
  clear eq67600
  have eq67602 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67601
       grind)
    | exact superpose eq67601 eq16
    | exact resolve eq16 eq67601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67601
  have eq69495 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq69500 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69495 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69495
  have eq69789 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq69500 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69500
  have eq69927 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69789 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq69789
    | exact resolve eq69789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69945 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69927 X0
       have i₂ := eq69789 X0
       grind)
    | exact superpose eq69789 eq69927
    | exact resolve eq69927 eq69789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69789 eq69927
  have eq70139 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq67602
       have i₂ := eq69945 x
       grind)
    | exact superpose eq69945 eq67602
    | (have r₁ := eq67602
       have r₂ := eq69945 x
       grind)
    | exact resolve eq67602 eq69945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67602 eq69945
  have eq70257 : False := by grind
  exact eq70257

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
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
  have eq30 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq83 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq86 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq55
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq181 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (k (σ X0) X1) (σ X2)
       have i₂ := eq30 X0 X1 X2
       grind)
    | exact superpose eq30 eq14
    | (have j0 := eq14 (k (σ X0) X1) (σ X2)
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq200 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq214 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op (M.op X2 X1) X1))) = (M.op (M.op (M.op X2 X1) X1) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X2 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq200 (M.op (M.op X2 X1) X1) X1 X3
       have i₂ := eq200 X1 X2 X0
       grind)
    | exact superpose eq200 eq200
    | exact resolve eq200 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq200 X1 x X3
       have i₂ := eq200 X1 x X0
       grind)
    | exact superpose eq200 eq200
    | exact resolve eq200 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq200 X1 x X0
       grind)
    | exact superpose eq200 eq9
    | exact resolve eq9 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 (M.op X2 X0) X2
       have i₂ := eq200 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq200 eq21
    | exact resolve eq21 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq230
    | exact resolve eq230 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq243 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) X1) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X2 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X0 X1 X2 x
       have i₂ := eq9 X1 x X2
       grind)
    | exact superpose eq9 eq214
    | exact resolve eq214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq253 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq225 X0 (M.op X0 X0)
       have i₂ := eq225 X0 X0
       grind)
    | exact superpose eq225 eq225
    | exact resolve eq225 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq225 X0 X1
       grind)
    | exact superpose eq225 eq21
    | exact resolve eq21 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq262 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259 X1 X0 X2
       have i₂ := eq225 X0 X1
       grind)
    | exact superpose eq225 eq259
    | exact resolve eq259 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq287 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq253 X0
       grind)
    | exact superpose eq253 eq9
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq287 X0 X1
       grind)
    | exact superpose eq287 eq225
    | exact resolve eq225 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq287 X0 X2
       grind)
    | exact superpose eq287 eq218
    | exact resolve eq218 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218 X1 (M.op X2 (M.op X2 X0)) X0
       have i₂ := eq225 X2 X0
       grind)
    | exact superpose eq225 eq218
    | exact resolve eq218 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq362 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X1 X0 (M.op X0 X0)
       have i₂ := eq253 X0
       grind)
    | exact superpose eq253 eq218
    | exact resolve eq218 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq253 X1
       have i₂ := eq239 X1 X0 X1
       grind)
    | (have i₁ := eq253 X1
       have i₂ := eq239 X1 X1 X0
       grind)
    | exact superpose eq239 eq253
    | exact resolve eq253 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq253
  have eq621 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq287 X0 X1
       grind)
    | exact superpose eq287 eq262
    | exact resolve eq262 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq699 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1 x
       have i₂ := eq355 X0 x X1
       grind)
    | exact superpose eq355 eq621
    | exact resolve eq621 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq621
  have eq1050 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X1 (M.op X0 X1)
       have i₂ := eq699 X1 X0
       grind)
    | (have i₁ := eq498 X1 (M.op X0 X0)
       have i₂ := eq699 X0 X1
       grind)
    | exact superpose eq699 eq498
    | exact resolve eq498 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1050 X0 X1
       have i₂ := eq312 X1 X0
       grind)
    | exact superpose eq312 eq1050
    | exact resolve eq1050 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq1050
  have eq1171 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) = (M.op (M.op (M.op X3 X1) X1) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 (M.op (M.op X1 X0) X0) X1 X0
       have i₂ := eq200 X0 X1 X2
       grind)
    | exact superpose eq200 eq86
    | exact resolve eq86 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1252 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1171 X0 X1 X2 X3
       have i₂ := eq243 X0 X1 X3
       grind)
    | exact superpose eq243 eq1171
    | exact resolve eq1171 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq1171
  have eq1282 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1)) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1252 X0 X1 x X3
       have i₂ := eq498 x (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))
       grind)
    | exact superpose eq498 eq1252
    | exact resolve eq1252 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1296 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op (M.op X3 X1) X1) (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1282 X0 X1 X3
       have i₂ := eq1055 (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1)
       grind)
    | exact superpose eq1055 eq1282
    | exact resolve eq1282 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1305 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) (M.op X1 X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1296 X0 X1 X3
       have i₂ := eq1055 (M.op X3 X1) X1
       grind)
    | exact superpose eq1055 eq1296
    | exact resolve eq1296 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq1296
  have eq1311 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1305 X0 X1 X3
       have i₂ := eq699 X1 (M.op X3 X1)
       grind)
    | exact superpose eq699 eq1305
    | exact resolve eq1305 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq1305
  have eq1315 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1311 X0 X1 x
       have i₂ := eq498 x X1
       grind)
    | exact superpose eq498 eq1311
    | exact resolve eq1311 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1530 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X2 (τ X1)) (τ X1))) X1) = (σ (M.op X0 (M.op X0 (τ X1)))) ∨ (τ X1) = (M.op (M.op X2 (τ X1)) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X1 (M.op (M.op X2 (τ X1)) (τ X1))
       have i₂ := eq200 (τ X1) X2 X0
       grind)
    | exact superpose eq200 eq83
    | (have j0 := eq83 X1 (M.op (M.op X2 (τ X1)) (τ X1))
       grind)
    | exact resolve eq83 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq200
  have eq1564 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 (τ X1)))) = (k (σ (M.op (τ X1) (τ X1))) X1) ∨ (τ X1) = (M.op (M.op X2 (τ X1)) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1530 X0 X1 X2
       have i₂ := eq498 X2 (τ X1)
       grind)
    | exact superpose eq498 eq1530
    | (have j0 := eq1530 X0 X1 X2
       grind)
    | exact resolve eq1530 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1573 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (σ (M.op X0 (M.op X0 (τ X1)))) = (k (σ (M.op (τ X1) (τ X1))) X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1564 X0 X1 x
       have i₂ := eq498 x (τ X1)
       grind)
    | exact superpose eq498 eq1564
    | (have j0 := eq1564 X0 X1 x
       grind)
    | exact resolve eq1564 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1574 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (τ X1)))) = (k (σ (M.op (τ X1) (τ X1))) X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1573 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq2573 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1315 X2 X1
       have i₂ := eq218 X1 X1 X0
       grind)
    | (have i₁ := eq1315 X2 X1
       have i₂ := eq218 X0 X1 X1
       grind)
    | exact superpose eq218 eq1315
    | exact resolve eq1315 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq7252 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (σ (k (τ (k X0 X1)) (τ (k X0 X1)))) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (τ X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq130
    | (have j0 := eq130 (τ X0) X1
       grind)
    | exact resolve eq130 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq7288 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (k (σ (τ (k X0 X1))) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7252 X0 X1
       have i₂ := eq19 (k X0 X1) (τ (k X0 X1))
       grind)
    | exact superpose eq19 eq7252
    | (have j0 := eq7252 X0 X1
       grind)
    | exact resolve eq7252 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7298 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (k (k X0 X1) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7288 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7288
    | (have j0 := eq7288 X0 X1
       grind)
    | exact resolve eq7288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288
  have eq7306 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7298 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7298
    | (have j0 := eq7298 X0 X1
       grind)
    | exact resolve eq7298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298
  have eq7309 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7306 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7306
    | (have j0 := eq7306 X0 X1
       grind)
    | exact resolve eq7306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7306
  have eq7310 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7309 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq7309 X0 X1
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq7309 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309
  have eq38842 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ (k X0 X1))) = (k (σ (k X0 X1)) (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7310 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7310
    | exact resolve eq7310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38845 : ∀ X0 X1 : G, (k (τ (k X0 X1)) (τ (k X0 X1))) = (M.op (τ (k X0 X1)) (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7310 (τ X1) (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq7310
    | exact resolve eq7310 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38869 : ∀ X0 X1 : G, (M.op (τ (k X0 X1)) (τ (k X0 X1))) = (τ (k (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38845 X0 X1
       have i₂ := eq34 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq34 eq38845
    | exact resolve eq38845 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq38845
  have eq38872 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ (k X0 X1))) = (σ (k (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38842 X0 X1
       have i₂ := eq15 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq15 eq38842
    | exact resolve eq38842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38842
  have eq38882 : ∀ X0 X1 : G, (M.op (τ (k X0 X1)) (τ (k X0 X1))) = (τ (M.op (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38869 X0 X1
       have i₂ := eq7310 X0 X1
       grind)
    | exact superpose eq7310 eq38869
    | exact resolve eq38869 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38869
  have eq38885 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ (k X0 X1))) = (σ (M.op (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38872 X0 X1
       have i₂ := eq7310 X0 X1
       grind)
    | exact superpose eq7310 eq38872
    | exact resolve eq38872 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7310 eq38872
  have eq211074 : ∀ X0 X1 : G, (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) = (τ (σ (M.op X0 (M.op X0 (τ (σ X1)))))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ (M.op (τ (σ X1)) (τ (σ X1)))) X1
       have i₂ := eq1574 X0 (σ X1)
       grind)
    | exact superpose eq1574 eq25
    | (have j1 := eq1574 X0 (σ X1)
       grind)
    | exact resolve eq25 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1574
  have eq211104 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (τ (σ X1)))) = (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq211074 X0 X1
       have i₂ := eq10 (M.op X0 (M.op X0 (τ (σ X1))))
       grind)
    | exact superpose eq10 eq211074
    | (have j0 := eq211074 X0 X1
       grind)
    | exact resolve eq211074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211074
  have eq211185 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (τ (σ X1)))) = (k (M.op (τ (σ X1)) (τ (σ X1))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq211104 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (τ (σ X1)))
       grind)
    | exact superpose eq10 eq211104
    | (have j0 := eq211104 X0 X1
       grind)
    | exact resolve eq211104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211104
  have eq211233 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X1 X1) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq211185 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq211185
    | (have j0 := eq211185 X0 X1
       grind)
    | exact resolve eq211185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211185
  have eq211256 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq211233 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq211233
    | (have j0 := eq211233 X0 X1
       grind)
    | exact resolve eq211233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211233
  have eq211329 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 (M.op X2 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq211256 X2 X0
       grind)
    | exact superpose eq211256 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq211256 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq211256 X0 X1
       grind)
    | exact resolve eq12 eq211256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211256
  have eq211715 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 (M.op X2 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq211329 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211329
  have eq416428 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X1 (M.op X1 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq211715 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211715
  have eq416430 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq416428 X0 X1
       grind)
    | (have r₁ := eq416428 x X0
       have r₂ := eq218 X0 x x
       grind)
    | (have r₁ := eq416428 X0 x
       have r₂ := eq218 X0 X0 x
       grind)
    | exact resolve eq416428 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq416428
  have eq417513 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X1 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416430 (M.op X1 X1) X2
       have i₂ := eq362 X1 X0
       grind)
    | exact superpose eq362 eq416430
    | exact resolve eq416430 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq417673 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X1 x X0
       have i₂ := eq416430 (M.op X0 (M.op X0 X1)) x
       grind)
    | exact superpose eq416430 eq356
    | exact resolve eq356 eq416430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq418038 : ∀ X0 X1 : G, (σ (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38885 (M.op X0 X0) X0
       have i₂ := eq416430 X0 X1
       grind)
    | exact superpose eq416430 eq38885
    | exact resolve eq38885 eq416430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416430
  have eq418103 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq418038 X0 X1
       have i₂ := eq2573 X0 X1 X0
       grind)
    | exact superpose eq2573 eq418038
    | exact resolve eq418038 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418038
  have eq418338 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq417673 X0 X1
       have i₂ := eq2573 X0 X1 X0
       grind)
    | exact superpose eq2573 eq417673
    | exact resolve eq417673 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417673
  have eq418446 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq417513 X0 X1 x
       have i₂ := eq287 X1 x
       grind)
    | exact superpose eq287 eq417513
    | exact resolve eq417513 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq417513
  have eq425191 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38882 (M.op X0 (M.op X0 x)) (M.op x x)
       have i₂ := eq418446 X0 x
       grind)
    | exact superpose eq418446 eq38882
    | exact resolve eq38882 eq418446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38882
  have eq425192 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38885 (M.op X0 (M.op X0 x)) (M.op x x)
       have i₂ := eq418446 X0 x
       grind)
    | exact superpose eq418446 eq38885
    | exact resolve eq38885 eq418446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38885
  have eq428327 : ∀ X0 X1 : G, (τ X0) = (k (M.op X1 (M.op X1 (τ X0))) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq418446 X1 (τ X0)
       have i₂ := eq425191 X0
       grind)
    | exact superpose eq425191 eq418446
    | exact resolve eq418446 eq425191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418446 eq425191
  have eq429210 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq498 (σ X0) (σ X0)
       have i₂ := eq425192 X0
       grind)
    | exact superpose eq425192 eq498
    | exact resolve eq498 eq425192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq463751 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq429210 (M.op X0 (M.op X0 X1))
       have i₂ := eq2573 X0 X1 X0
       grind)
    | exact superpose eq2573 eq429210
    | exact resolve eq429210 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573 eq429210
  have eq473230 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (M.op X1 (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq463751 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq463751
    | exact resolve eq463751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463751
  have eq476373 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (M.op X1 (τ X0)))) (σ (M.op X1 (M.op X1 (τ X0))))) = (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq418338 X0 (σ (M.op X1 (M.op X1 (τ X0))))
       have i₂ := eq473230 X0 X1
       grind)
    | exact superpose eq473230 eq418338
    | exact resolve eq418338 eq473230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418338 eq473230
  have eq476397 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq476373 X0 X1
       have i₂ := eq418103 X1 (τ X0)
       grind)
    | exact superpose eq418103 eq476373
    | exact resolve eq476373 eq418103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418103 eq476373
  have eq476669 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq476397 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq476397
    | exact resolve eq476397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476397
  have eq627681 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0))) ∨ (σ X2) = (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 (M.op X1 (M.op X1 (τ X0))) (M.op X0 X0) X2
       have i₂ := eq428327 X0 X1
       grind)
    | exact superpose eq428327 eq181
    | (have j0 := eq181 (M.op X1 (M.op X1 (τ X0))) (M.op X0 X0) X2
       grind)
    | exact resolve eq181 eq428327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq428327
  have eq627718 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq627681 X0 X1 X2
       have i₂ := eq476669 X0 X1
       grind)
    | exact superpose eq476669 eq627681
    | (have j0 := eq627681 X0 X1 X2
       grind)
    | exact resolve eq627681 eq476669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627681
  have eq627903 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq627718 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq627718
    | (have j0 := eq627718 X0 X1 X2
       grind)
    | exact resolve eq627718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq627718
  have eq628039 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (k (σ (M.op X1 (M.op X1 (τ X0)))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq627903 X0 X1 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq627903 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq627903 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627903
  have eq628117 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq628039 X0 x X2
       have i₂ := eq476669 X0 x
       grind)
    | exact superpose eq476669 eq628039
    | (have j0 := eq628039 X0 x X2
       grind)
    | exact resolve eq628039 eq476669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476669 eq628039
  have eq628241 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq628117 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq628117
    | exact resolve eq628117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628356 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq628117 (σ X1) X0
       grind)
    | exact superpose eq628117 eq15
    | (have j1 := eq628117 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq628117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628117
  have eq629379 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq628241 (τ X0) X1
       grind)
    | exact superpose eq628241 eq19
    | (have j1 := eq628241 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq628241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq628241
  have eq732849 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq629379 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629379
    | exact resolve eq629379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629379
  have eq733415 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq732849 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq732849
    | (have j0 := eq732849 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq732849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732849
  have eq1099147 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq628356 x y
       grind)
    | exact superpose eq628356 eq16
    | (have j1 := eq628356 x y
       grind)
    | exact resolve eq16 eq628356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628356
  have eq1101370 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1099147
       have i₂ := eq733415 x y
       grind)
    | exact superpose eq733415 eq1099147
    | (have j1 := eq733415 (σ x) (σ y)
       grind)
    | (have r₁ := eq1099147
       have r₂ := eq733415 x y
       grind)
    | (have r₁ := eq1099147
       have r₂ := eq733415 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1099147
       have r₂ := eq733415 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1099147 eq733415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733415 eq1099147
  have eq1101381 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1101370
  have eq1101423 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1101381
       grind)
    | exact superpose eq1101381 eq16
    | exact resolve eq16 eq1101381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101381
  have eq1101424 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1101423
       have r₂ := eq425192 x
       grind)
    | exact resolve eq1101423 eq425192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101423
  have eq1102864 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1101424
       grind)
    | exact superpose eq1101424 eq16
    | exact resolve eq16 eq1101424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102865 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1101424
       grind)
    | exact superpose eq1101424 eq10
    | exact resolve eq10 eq1101424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101424
  have eq1103117 : x = y := by
    first
    | (have i₁ := eq1102865
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1102865
    | exact resolve eq1102865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102865
  have eq1103118 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1102864
       have i₂ := eq425192 x
       grind)
    | exact superpose eq425192 eq1102864
    | exact resolve eq1102864 eq425192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425192 eq1102864
  have eq1103180 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1103118
       have i₂ := eq1103117
       grind)
    | exact superpose eq1103117 eq1103118
    | exact resolve eq1103118 eq1103117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103117 eq1103118
  have eq1103181 : False := by grind
  exact eq1103181

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq83 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
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
  have eq154 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq161 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq154
    | (have j0 := eq154 X0 X1
       grind)
    | exact resolve eq154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq344 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq83
    | exact resolve eq83 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq370 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq344 X1 x X0
       grind)
    | exact superpose eq344 eq9
    | exact resolve eq9 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq402 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq370 X0 (M.op X0 X0)
       have i₂ := eq370 X0 X0
       grind)
    | exact superpose eq370 eq370
    | exact resolve eq370 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq402 X0
       grind)
    | exact superpose eq402 eq9
    | exact resolve eq9 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq441 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq167 x y
       grind)
    | exact superpose eq167 eq16
    | (have j1 := eq167 x y
       grind)
    | exact resolve eq16 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3819 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq441
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq441
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq441
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq441
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq441 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq3820 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by grind
  clear eq3819
  have eq56640 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3820
       grind)
    | exact superpose eq3820 eq10
    | exact resolve eq10 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3820
  have eq56755 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq56640
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq56640
    | exact resolve eq56640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56640
  have eq56756 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq56755
  have eq86134 : y = (M.op y (M.op y (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq370 y y
       have i₂ := eq56756
       grind)
    | exact superpose eq56756 eq370
    | exact resolve eq370 eq56756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq56756
  have eq86266 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq86134
       have i₂ := eq420 x y
       grind)
    | exact superpose eq420 eq86134
    | exact resolve eq86134 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq86134
  have eq86267 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq86266
  have eq86357 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq86267
       grind)
    | exact superpose eq86267 eq10
    | exact resolve eq10 eq86267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86267
  have eq86474 : x = y ∨ x = y := by
    first
    | (have i₁ := eq86357
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq86357
    | exact resolve eq86357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86357
  have eq86475 : x = y := by grind
  clear eq86474
  have eq86485 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86475
       grind)
    | exact superpose eq86475 eq16
    | exact resolve eq16 eq86475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86475
  have eq86486 : False := by grind
  exact eq86486

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq43
    | exact resolve eq43 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43
  have eq135 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq20 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq20 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq284 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq26
    | (have j0 := eq26 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq327 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq867 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (σ X0) (σ X0) X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq135
    | exact resolve eq135 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq327 x y
       grind)
    | exact superpose eq327 eq16
    | (have j1 := eq327 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq327 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq34086 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq33824
  have eq37217 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq135 (σ x) (σ y) X0
       have i₂ := eq34086
       grind)
    | exact superpose eq34086 eq135
    | exact resolve eq135 eq34086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34086
  have eq37270 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq37217 x
       have i₂ := eq867 x x
       grind)
    | exact superpose eq867 eq37217
    | exact resolve eq37217 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq37217
  have eq37271 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq37270
  have eq52793 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq135 x y X0
       have i₂ := eq37271
       grind)
    | exact superpose eq37271 eq135
    | exact resolve eq135 eq37271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37271
  have eq52861 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52793 x
       have i₂ := eq135 x x x
       grind)
    | exact superpose eq135 eq52793
    | exact resolve eq52793 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq52793
  have eq52862 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq52861
  have eq63938 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52862
       grind)
    | exact superpose eq52862 eq10
    | exact resolve eq10 eq52862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52862
  have eq64020 : x = y ∨ x = y := by
    first
    | (have i₁ := eq63938
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63938
    | exact resolve eq63938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63938
  have eq64021 : x = y := by grind
  clear eq64020
  have eq84333 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64021
       grind)
    | exact superpose eq64021 eq16
    | exact resolve eq16 eq64021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64021
  have eq84334 : False := by grind
  exact eq84334

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op (M.op X2 X2) X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X2 X2) X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq65
    | (have j0 := eq65 X0 (σ X1)
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq71
    | (have j1 := eq65 x x
       grind)
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq121 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq40
    | exact resolve eq40 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq304 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq65 X1 (τ X0)
       grind)
    | exact superpose eq65 eq38
    | (have j1 := eq65 X0 (τ X0)
       grind)
    | exact resolve eq38 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq363 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X2 X3 (M.op X1 X1)
       have i₂ := eq51 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq51 X2 X3 (M.op X1 X1)
       have i₂ := eq51 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq259
    | exact resolve eq259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X1) X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq558 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq50 X1 X4 x x
       have i₂ := eq50 X1 X0 x x
       grind)
    | (have i₁ := eq50 X0 X1 x x
       have i₂ := eq50 X0 (M.op x x) x x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq50 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq93 eq65
    | (have j0 := eq65 x (σ x)
       grind)
    | exact resolve eq65 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq595
    | exact resolve eq595 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq599 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq596
       have r₂ := eq27
       grind)
    | exact resolve eq596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq607 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq599 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq599
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq599
       grind)
    | exact resolve eq13 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq608 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq607
  have eq654 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq608 eq49
    | exact resolve eq49 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq608
  have eq675 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq671
    | exact resolve eq671 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq671
  have eq678 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq65
    | (have j0 := eq65 x x
       grind)
    | exact resolve eq65 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq679 : x = (M.op x x) := by grind
  clear eq678
  have eq684 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 x X0
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq51
    | exact resolve eq51 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq688 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq679
       grind)
    | exact resolve eq13 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : x = (k x x) := by grind
  clear eq688
  have eq692 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq689
       grind)
    | exact superpose eq689 eq43
    | exact resolve eq43 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq689
  have eq696 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq692
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq692
    | exact resolve eq692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq692
  have eq699 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq696 eq65
    | (have j0 := eq65 x (σ x)
       grind)
    | exact resolve eq65 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq700 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq699
  have eq707 : ∀ X0 : G, (k (M.op X0 (M.op x X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq462 X0 x
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq462
    | exact resolve eq462 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq740 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq700 eq684
    | exact resolve eq684 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq942 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq26 eq740
    | (have j0 := eq740 (σ y)
       grind)
    | exact resolve eq740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1 x
       have i₂ := eq684 x (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq684 eq576
    | exact resolve eq576 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq997 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) X0)) = (M.op x (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq988 X1 (M.op X1 (M.op (M.op X2 X2) X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq988
    | exact resolve eq988 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 X1 : G, (σ X0) = (M.op x (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq988 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq988
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq988 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1009 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq988 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq988
    | (have j0 := eq988 x y
       grind)
    | exact resolve eq988 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : (σ y) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq988
    | (have j0 := eq988 (σ x) (σ y)
       grind)
    | exact resolve eq988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1040 : (σ y) = (M.op x (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq740 eq1012
    | exact resolve eq1012 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq1012
  have eq1047 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X1 x
       have i₂ := eq684 x X0
       grind)
    | exact superpose eq684 eq997
    | exact resolve eq997 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1050 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1009
       have i₂ := eq558 x sF0 x
       grind)
    | (have i₁ := eq1009
       have i₂ := eq558 X0 sF0 x
       grind)
    | exact superpose eq558 eq1009
    | exact resolve eq1009 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1061 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1040
       have i₂ := eq558 x sF4 x
       grind)
    | (have i₁ := eq1040
       have i₂ := eq558 X0 sF4 x
       grind)
    | exact superpose eq558 eq1040
    | exact resolve eq1040 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1090 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1050 eq988
    | exact resolve eq988 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1149 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op x (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1061 eq988
    | exact resolve eq988 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1061 eq558
    | exact resolve eq558 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq1061
  have eq1768 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ y)) = (σ (M.op y (k (τ X0) X1))) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq65 (k (τ X0) X1) y
       grind)
    | exact superpose eq65 eq264
    | (have j1 := eq65 X0 y
       grind)
    | exact resolve eq264 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq264
  have eq1929 : (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq942 eq707
    | exact resolve eq707 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1949 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op x (σ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq259 (M.op (σ X0) (M.op x (σ X0))) X0
       have i₂ := eq707 (σ X0)
       grind)
    | exact superpose eq707 eq259
    | exact resolve eq259 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq1954 : ∀ X0 : G, (k (τ (M.op (σ X0) (M.op x (σ X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1949 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1949
    | exact resolve eq1949 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq3127 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op x (M.op X1 X1)) X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq363 x X1 X2 X3
       have i₂ := eq684 x (M.op X1 X1)
       grind)
    | exact superpose eq684 eq363
    | exact resolve eq363 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq3128 : ∀ X1 X2 : G, (M.op x X2) = (M.op (M.op x (M.op X1 X1)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq3127 X1 X2 x
       have i₂ := eq684 x X2
       grind)
    | exact superpose eq684 eq3127
    | exact resolve eq3127 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3145 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq1149 eq3128
    | exact resolve eq3128 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3177 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (k (M.op x (M.op (M.op X0 X0) (M.op x (M.op X1 X1)))) (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq462 (M.op x (M.op X1 X1)) X0
       have i₂ := eq3128 X1 (M.op (M.op X0 X0) (M.op x (M.op X1 X1)))
       grind)
    | exact superpose eq3128 eq462
    | exact resolve eq462 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq3128
  have eq3231 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (k (M.op x (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))) (M.op x (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X1
       have i₂ := eq1047 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact superpose eq1047 eq3177
    | exact resolve eq3177 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq3273 : ∀ X1 : G, (M.op x (M.op X1 X1)) = (k (M.op X1 X1) (M.op x (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq3231 x X1
       have i₂ := eq14 (M.op X1 X1) x x
       grind)
    | exact superpose eq14 eq3231
    | exact resolve eq3231 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq6569 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq654 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq654
    | (have j0 := eq654 (τ X0)
       grind)
    | exact resolve eq654 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6580 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6569 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6569
    | (have j0 := eq6569 X0
       grind)
    | exact resolve eq6569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6569
  have eq6586 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6580 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6580
    | (have j0 := eq6580 X0
       grind)
    | exact resolve eq6580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq7551 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op (τ X1) (M.op (M.op X2 X2) X0))) X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq304 X1 (M.op (τ X1) (M.op (M.op X2 X2) X0))
       have i₂ := eq14 X0 (τ X1) X2
       grind)
    | exact superpose eq14 eq304
    | (have j0 := eq304 X1 X1
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq7605 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ X1) (M.op x X0))) X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7551 X0 X1 x
       have i₂ := eq684 x X0
       grind)
    | exact superpose eq684 eq7551
    | (have j0 := eq7551 X0 X1 x
       grind)
    | exact resolve eq7551 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq7551
  have eq7613 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op x (M.op (τ X1) X0))) X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7605 X0 X1
       have i₂ := eq1047 X0 (τ X1)
       grind)
    | exact superpose eq1047 eq7605
    | (have j0 := eq7605 X0 X1
       grind)
    | exact resolve eq7605 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7605
  have eq8100 : ∀ X0 : G, (k (τ (M.op x (M.op (σ X0) (σ X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1954 X0
       have i₂ := eq1047 (σ X0) (σ X0)
       grind)
    | exact superpose eq1047 eq1954
    | exact resolve eq1954 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq1954
  have eq8207 : ∀ X0 : G, (τ X0) = (k (τ (M.op x (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8100 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8100
    | exact resolve eq8100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100
  have eq8351 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (τ (M.op x (M.op x (M.op (σ y) (M.op (σ x) (σ y)))))) (τ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3145 eq8207
    | exact resolve eq8207 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145 eq8207
  have eq8433 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1150 eq8351
    | exact resolve eq8351 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq8351
  have eq21089 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1149 eq3273
    | exact resolve eq3273 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq3273
  have eq52356 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op x (M.op (τ (σ X1)) X0)))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (σ (M.op x (M.op (τ (σ X1)) X0))) X1
       have i₂ := eq7613 X0 (σ X1)
       grind)
    | exact superpose eq7613 eq259
    | (have j1 := eq7613 X0 (σ X1)
       grind)
    | exact resolve eq259 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq7613
  have eq52384 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op x (M.op (τ (σ X1)) X0)) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52356 X0 X1
       have i₂ := eq16 (M.op x (M.op (τ (σ X1)) X0))
       grind)
    | exact superpose eq16 eq52356
    | (have j0 := eq52356 X0 X1
       grind)
    | exact resolve eq52356 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52356
  have eq52455 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op x (M.op X1 X0)) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52384 X0 X1
       have i₂ := eq16 X1
       grind)
    | exact superpose eq16 eq52384
    | (have j0 := eq52384 X0 X1
       grind)
    | exact resolve eq52384 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52384
  have eq52471 : ∀ X0 X1 : G, (k (M.op x (M.op X1 X0)) X1) = X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52455 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq52455
    | (have j0 := eq52455 X0 X1
       grind)
    | exact resolve eq52455 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52455
  have eq52478 : ∀ X0 X1 : G, (k (M.op x (M.op X1 X0)) X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52471 X0 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq52471
    | (have j0 := eq52471 X0 X1
       grind)
    | exact resolve eq52471 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52471
  have eq220325 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X1)) (σ (τ (k X0 X1))))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 (τ X0) (τ X1)
       have i₂ := eq404 X1 X0
       grind)
    | exact superpose eq404 eq1006
    | (have j0 := eq1006 X0 (τ X1)
       grind)
    | exact resolve eq1006 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq1006
  have eq220342 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X1)) (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq220325 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq220325
    | (have j0 := eq220325 X0 X1
       grind)
    | exact resolve eq220325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220325
  have eq220507 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op x (M.op X1 (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq220342 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq220342
    | (have j0 := eq220342 X0 X1
       grind)
    | exact resolve eq220342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220342
  have eq220650 : ∀ X0 X1 : G, (M.op x (M.op X1 (k X0 X1))) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq220507 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq220507
    | (have j0 := eq220507 X0 X1
       grind)
    | exact resolve eq220507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220507
  have eq220716 : ∀ X0 X1 : G, (M.op x (M.op X1 (k X0 X1))) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq220650 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq220650
    | (have j0 := eq220650 X0 X1
       grind)
    | exact resolve eq220650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220650
  have eq446589 : (k (k (M.op (σ y) (σ y)) (σ (τ (M.op (σ y) (M.op (σ x) (σ y)))))) (σ y)) = (σ (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y)))))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8433 eq1768
    | exact resolve eq1768 eq8433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768 eq8433
  have eq446824 : (k (k (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) = (σ (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y)))))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq446589
       have i₂ := eq15 (M.op sF3 sF4)
       grind)
    | exact superpose eq15 eq446589
    | exact resolve eq446589 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446589
  have eq446864 : (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (σ (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y)))))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21089 eq446824
    | exact resolve eq446824 eq21089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21089 eq446824
  have eq446892 : (σ y) = (σ (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y)))))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1929 eq446864
    | exact resolve eq446864 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929 eq446864
  have eq448198 : (τ (σ y)) = (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq446892 eq16
    | exact resolve eq16 eq446892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446892
  have eq448387 : y = (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq448198
    | exact resolve eq448198 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448198
  have eq448458 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq448387 eq52478
    | (have j0 := eq52478 x y
       grind)
    | exact resolve eq52478 eq448387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52478 eq448387
  have eq448462 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq448458
  have eq448475 : (k (M.op x y) y) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq448462
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq448462
    | exact resolve eq448462 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq448462
  have eq449560 : (σ (k (M.op x y) y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq448475 eq15
    | exact resolve eq15 eq448475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448475
  have eq449814 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq121 eq449560
    | exact resolve eq449560 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq449560
  have eq449864 : (σ (M.op x y)) = (M.op x (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq449814 eq220716
    | (have j0 := eq220716 x (σ y)
       grind)
    | exact resolve eq220716 eq449814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220716 eq449814
  have eq449868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq449864
       have i₂ := eq988 sF3 sF4
       grind)
    | exact superpose eq988 eq449864
    | exact resolve eq449864 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449864
  have eq449882 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq449868
       have r₂ := eq27
       grind)
    | exact resolve eq449868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449868
  have eq449966 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq449882 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq449882
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq449882
       grind)
    | exact resolve eq13 eq449882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449882
  have eq450016 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq449966
  have eq451601 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq450016 eq99
    | exact resolve eq99 eq450016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq450016
  have eq451766 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq451601
    | exact resolve eq451601 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq451601
  have eq451769 : y = (M.op y y) := by
    first
    | (have j1 := eq6586 y
       grind)
    | (have r₁ := eq451766
       have r₂ := eq6586 y
       grind)
    | exact resolve eq451766 eq6586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586 eq451766
  have eq451842 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq451769
       grind)
    | exact superpose eq451769 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq451769
       grind)
    | exact resolve eq13 eq451769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451847 : y = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq988 y y
       have i₂ := eq451769
       grind)
    | exact superpose eq451769 eq988
    | exact resolve eq988 eq451769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451769
  have eq451892 : y = (k y y) := by grind
  clear eq451842
  have eq451939 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq451847
       have i₂ := eq1090 y
       grind)
    | exact superpose eq1090 eq451847
    | exact resolve eq451847 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451847
  have eq452132 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq654 y
       have i₂ := eq451892
       grind)
    | exact superpose eq451892 eq654
    | (have j0 := eq654 y
       grind)
    | exact resolve eq654 eq451892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq451892
  have eq452256 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq452132
  have eq452342 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq452256
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq452256
    | exact resolve eq452256 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452256
  have eq452568 : (M.op x y) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq451939 eq988
    | exact resolve eq988 eq451939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452659 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq452568
       have i₂ := eq1090 y
       grind)
    | exact superpose eq1090 eq452568
    | exact resolve eq452568 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq452568
  have eq452721 : y = (M.op x y) := by
    first
    | exact superpose eq451939 eq452659
    | exact resolve eq452659 eq451939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451939 eq452659
  have eq452768 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq452721 eq20
    | exact resolve eq20 eq452721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq452721
  have eq453185 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq452768
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq452768
    | exact resolve eq452768 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq452768
  have eq453291 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq453185 eq942
    | exact resolve eq942 eq453185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq457002 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq453185 eq452342
    | exact resolve eq452342 eq453185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452342 eq453185
  have eq461461 : (σ (M.op x y)) = (M.op x (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq457002 eq988
    | exact resolve eq988 eq457002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq461549 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq457002 eq461461
    | exact resolve eq461461 eq457002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457002 eq461461
  have eq467102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq461549 eq453291
    | exact resolve eq453291 eq461549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453291 eq461549
  have eq467103 : False := by grind
  exact eq467103

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq192 : (σ (k (k (M.op x y) x) (M.op x y))) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq121 eq42
    | exact resolve eq42 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq121
  have eq478 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq634 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq641 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq642 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq648 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq651 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq648 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq648
    | (have j0 := eq648 X0
       grind)
    | exact resolve eq648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq711 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq478
    | (have j0 := eq478 X0 (σ y) (σ x)
       grind)
    | exact resolve eq478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq711 (M.op x x)
       have i₂ := eq52 sF3 X1 x
       grind)
    | (have i₁ := eq711 (M.op X1 X1)
       have i₂ := eq52 sF3 X1 x
       grind)
    | exact superpose eq52 eq711
    | exact resolve eq711 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq815 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq496 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq496
    | (have j0 := eq496 x y X0
       grind)
    | exact resolve eq496 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq496
    | (have j0 := eq496 (σ x) (σ y) X0
       grind)
    | exact resolve eq496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4504 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq642 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq642
    | (have j0 := eq642 (τ X0)
       grind)
    | exact resolve eq642 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4512 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4504 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4504
    | (have j0 := eq4504 X0
       grind)
    | exact resolve eq4504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq4518 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4512 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4512
    | (have j0 := eq4512 X0
       grind)
    | exact resolve eq4512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512
  have eq6770 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq496 X2 X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)))
       have i₂ := eq483 X1 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq483 eq496
    | exact resolve eq496 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq22767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22767
    | exact resolve eq22767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22767
  have eq22779 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22768
       have r₂ := eq28
       grind)
    | exact resolve eq22768 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22768
  have eq22784 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq22779
  have eq22865 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22784
    | exact resolve eq22784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22784
  have eq23111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22865 eq92
    | exact resolve eq92 eq22865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq22865
  have eq23120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23111
  have eq23123 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq23120
       have r₂ := eq28
       grind)
    | exact resolve eq23120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23120
  have eq23128 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  have eq23445 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23128 eq50
    | exact resolve eq50 eq23128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23128
  have eq24585 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23123 eq23445
    | exact resolve eq23445 eq23123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23123 eq23445
  have eq24643 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq24585
  have eq24651 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq24643
    | exact resolve eq24643 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24643
  have eq24652 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq4518 x
       grind)
    | (have r₁ := eq24651
       have r₂ := eq4518 x
       grind)
    | exact resolve eq24651 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518 eq24651
  have eq24653 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq24652
       grind)
    | exact superpose eq24652 eq84
    | exact resolve eq84 eq24652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq24656 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  have eq24724 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq24652
  have eq24738 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24656
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24656
    | exact resolve eq24656 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24656
  have eq24739 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24653
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24653
    | exact resolve eq24653 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24653
  have eq25631 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq24738
       grind)
    | exact superpose eq24738 eq68
    | exact resolve eq68 eq24738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24738
  have eq25651 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq25631
    | exact resolve eq25631 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25631
  have eq25938 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24739
       have r₂ := eq24724
       grind)
    | exact resolve eq24739 eq24724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24724 eq24739
  have eq25944 : (τ (σ y)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25938 eq50
    | exact resolve eq50 eq25938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq25972 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq25944
    | exact resolve eq25944 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25944
  have eq25992 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq651 x
       have i₂ := eq25972
       grind)
    | exact superpose eq25972 eq651
    | (have j0 := eq651 x
       grind)
    | exact resolve eq651 eq25972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq25972
  have eq26000 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25992
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq25992
    | exact resolve eq25992 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq25992
  have eq26015 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26000
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26000
    | exact resolve eq26000 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26000
  have eq26021 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26015
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26015
    | exact resolve eq26015 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26015
  have eq26023 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq26021
    | exact resolve eq26021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26021
  have eq26024 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26023
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26023
    | exact resolve eq26023 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26023
  have eq34405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26024 eq25651
    | exact resolve eq25651 eq26024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26024
  have eq34408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq34405
  have eq34419 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq34408
       have r₂ := eq28
       grind)
    | exact resolve eq34408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34408
  have eq34426 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq34419
  have eq34564 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq34426 eq25938
    | exact resolve eq25938 eq34426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25938 eq34426
  have eq34584 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq34564
  have eq34597 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq34584
  have eq34725 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq34597
    | exact resolve eq34597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq34597
  have eq34876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq34725 eq25651
    | exact resolve eq25651 eq34725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25651 eq34725
  have eq34878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq34876
  have eq34888 : x = (M.op x x) := by
    first
    | (have r₁ := eq34878
       have r₂ := eq28
       grind)
    | exact resolve eq34878 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34878
  have eq36061 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq34888
       grind)
    | exact superpose eq34888 eq12
    | (have j0 := eq12 (k X0 x) X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq34888
       grind)
    | exact resolve eq12 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36063 : (k x x) = (M.op x x) := by grind
  have eq36066 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x
       have i₂ := eq34888
       grind)
    | exact superpose eq34888 eq52
    | exact resolve eq52 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq36121 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq815 x
       have i₂ := eq34888
       grind)
    | exact superpose eq34888 eq815
    | exact resolve eq815 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq36134 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq478 X0 x x
       have i₂ := eq34888
       grind)
    | exact superpose eq34888 eq478
    | exact resolve eq478 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36148 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq36061 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36061
  have eq36158 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq36134 X0
       have i₂ := eq34888
       grind)
    | exact superpose eq34888 eq36134
    | exact resolve eq36134 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36134
  have eq36163 : x = (k x x) := by
    first
    | (have i₁ := eq36063
       have i₂ := eq34888
       grind)
    | exact superpose eq34888 eq36063
    | exact resolve eq36063 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34888 eq36063
  have eq36185 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq642 x
       have i₂ := eq36163
       grind)
    | exact superpose eq36163 eq642
    | (have j0 := eq642 x
       grind)
    | exact resolve eq642 eq36163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq36163
  have eq36195 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq36185
  have eq36204 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36195
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36195
    | exact resolve eq36195 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36195
  have eq36225 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq36204 eq12
    | (have j0 := eq12 (k X0 (σ x)) X0
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq36204
       grind)
    | exact resolve eq12 eq36204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36286 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq36204 eq816
    | exact resolve eq816 eq36204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36320 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have j0 := eq36225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36225
  have eq37352 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq36121
       have i₂ := eq478 x sF0 x
       grind)
    | (have i₁ := eq36121
       have i₂ := eq478 X0 sF0 x
       grind)
    | exact superpose eq478 eq36121
    | exact resolve eq36121 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq36121
  have eq38324 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36286 eq496
    | exact resolve eq496 eq36286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq36286
  have eq43083 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op x X1) X1) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq6770 x X1 X2 X3
       have i₂ := eq36066 X1 x
       grind)
    | exact superpose eq36066 eq6770
    | exact resolve eq6770 eq36066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6770 eq36066
  have eq43218 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ y)) = (M.op (M.op (M.op x X0) X0) (M.op (M.op X1 X1) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq779 eq43083
    | exact resolve eq43083 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq43703 : ∀ X0 X2 : G, (M.op (M.op X2 X2) (σ y)) = (M.op (M.op (M.op x X0) X0) (σ y)) := by
    intro X0 X2
    first
    | exact superpose eq816 eq43218
    | exact resolve eq43218 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq43218
  have eq43826 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op x X0) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq38324 eq43703
    | exact resolve eq43703 eq38324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43703
  have eq79941 : (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq192
       have i₂ := eq36148 sF0
       grind)
    | exact superpose eq36148 eq192
    | (have j1 := eq36148 (M.op x y)
       grind)
    | exact resolve eq192 eq36148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq36148
  have eq79951 : (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq79941
  have eq80127 : (σ y) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37352 eq79951
    | exact resolve eq79951 eq37352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79951
  have eq80220 : (σ y) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80127
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80127
    | exact resolve eq80127 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80127
  have eq80884 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36320 eq80220
    | (have j1 := eq36320 (σ (M.op x y))
       grind)
    | exact resolve eq80220 eq36320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36320 eq80220
  have eq80911 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq80884
  have eq380845 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op x X0) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq80911 eq43083
    | exact resolve eq43083 eq80911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43083 eq80911
  have eq380972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq43826 eq380845
    | exact resolve eq380845 eq43826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43826 eq380845
  have eq381016 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq380972
       have r₂ := eq28
       grind)
    | exact resolve eq380972 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380972
  have eq381053 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq381016 eq29
    | exact resolve eq29 eq381016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq381016
  have eq381430 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq381053
    | exact resolve eq381053 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq381053
  have eq381431 : x = (M.op x y) := by grind
  clear eq381430
  have eq381450 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq381431 eq21
    | exact resolve eq21 eq381431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq381655 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq381431 eq37352
    | exact resolve eq37352 eq381431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37352 eq381431
  have eq381811 : x = y := by
    first
    | (have i₁ := eq381655 x
       have i₂ := eq36158 x
       grind)
    | exact superpose eq36158 eq381655
    | exact resolve eq381655 eq36158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36158 eq381655
  have eq381974 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq381450
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq381450
    | exact resolve eq381450 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381450
  have eq382113 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq381811
       grind)
    | exact superpose eq381811 eq25
    | exact resolve eq25 eq381811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq381811
  have eq382701 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq382113
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq382113
    | exact resolve eq382113 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq382113
  have eq382937 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq381974 eq36204
    | exact resolve eq36204 eq381974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36204
  have eq386130 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq381974 eq382701
    | exact resolve eq382701 eq381974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381974 eq382701
  have eq401362 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq382937 eq38324
    | exact resolve eq38324 eq382937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38324
  have eq401490 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq386130 eq401362
    | exact resolve eq401362 eq386130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386130 eq401362
  have eq401593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq382937 eq401490
    | exact resolve eq401490 eq382937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382937 eq401490
  have eq401659 : False := by grind
  exact eq401659

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq67
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq67 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq49
    | exact resolve eq49 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq120 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq117
    | exact resolve eq117 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq117
  have eq562 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq50 X1 X4 x x
       have i₂ := eq50 X1 X0 x x
       grind)
    | (have i₁ := eq50 X0 X1 x x
       have i₂ := eq50 X0 (M.op x x) x x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq50 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq100 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq100
  have eq818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq817
    | exact resolve eq817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq821 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq818
       have r₂ := eq27
       grind)
    | exact resolve eq818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq823 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq821
    | exact resolve eq821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq829 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) X1))) = X1 ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq823 eq14
    | exact resolve eq14 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ x))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq823 eq562
    | exact resolve eq562 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1158 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1069 eq829
    | exact resolve eq829 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq1069
  have eq1174 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1158
  have eq1193 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X1))) = X1 ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq823 eq581
    | exact resolve eq581 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq1266 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1193
    | (have j0 := eq1193 (σ x) (σ y)
       grind)
    | exact resolve eq1193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1316 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1266 eq1174
    | exact resolve eq1174 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq1266
  have eq1325 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq1316
  have eq1338 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X0 X1))) = X1 ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1 x
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq581
    | exact resolve eq581 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq1653 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1338 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1338
    | (have j0 := eq1338 x y
       grind)
    | exact resolve eq1338 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1654 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1338 x x
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq1338
    | exact resolve eq1338 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325 eq1338
  have eq1701 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq1654
  have eq1837 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1701 eq1653
    | exact resolve eq1653 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653 eq1701
  have eq1847 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1837
  have eq1850 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1847 eq29
    | exact resolve eq29 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1847
  have eq1869 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1850
    | exact resolve eq1850 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1850
  have eq1870 : x = y := by grind
  clear eq1869
  have eq1875 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1870
       grind)
    | exact superpose eq1870 eq18
    | exact resolve eq18 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1876 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1870
       grind)
    | exact superpose eq1870 eq24
    | exact resolve eq24 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1870
  have eq1897 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1876
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1876
    | exact resolve eq1876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1876
  have eq1904 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1897 eq26
    | exact resolve eq26 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1897
  have eq1952 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1904 eq120
    | exact resolve eq120 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1904
  have eq1972 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1952
       have i₂ := eq1875
       grind)
    | exact superpose eq1875 eq1952
    | exact resolve eq1952 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875 eq1952
  have eq1978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1972 eq15
    | exact resolve eq15 eq1972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq2005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1978
    | exact resolve eq1978 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1978
  have eq2011 : False := by grind
  exact eq2011

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53
  have eq153 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq157 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq153 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq153 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq153 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq153
  have eq355 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq157 (σ X1) (σ X0)
       grind)
    | exact superpose eq157 eq15
    | exact resolve eq15 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq157 X1 X0
       grind)
    | exact superpose eq157 eq355
    | exact resolve eq355 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq355
  have eq365 : False := by grind
  exact eq365
