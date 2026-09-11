import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq405 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq321
    | exact resolve eq321 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq603 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq625 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq625 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq625 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq629 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq16
    | exact resolve eq16 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq175
    | exact resolve eq175 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 : G, (M.op y (M.op (M.op x y) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq174
    | exact resolve eq174 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq16
    | exact resolve eq16 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq626 (M.op X0 X0)
       grind)
    | exact superpose eq626 eq16
    | exact resolve eq16 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq633 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq633
    | exact resolve eq633 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq643 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq626 X1
       grind)
    | exact superpose eq626 eq629
    | exact resolve eq629 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq740 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq632 (k (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq642 (M.op X0 X1)
       grind)
    | exact superpose eq642 eq632
    | exact resolve eq632 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq643 X0 (k (k X0 X0) (k X0 X0))
       have i₂ := eq642 (k X0 X0)
       grind)
    | exact superpose eq642 eq643
    | exact resolve eq643 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (k X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq630 eq177
    | exact resolve eq177 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq174
    | exact resolve eq174 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X3
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq993 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq993
    | exact resolve eq993 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1007 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq988 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq988
    | exact resolve eq988 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq603
       grind)
    | exact superpose eq603 eq40
    | exact resolve eq40 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1075
    | exact resolve eq1075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1078 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1076
    | exact resolve eq1076 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1161 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1007 eq632
    | exact resolve eq632 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1171 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1161 X0
       have i₂ := eq626 (k (k X0 X0) (k X0 X0))
       grind)
    | exact superpose eq626 eq1161
    | exact resolve eq1161 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1174 : ∀ X0 : G, (M.op (k X0 X0) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1171 X0
       have i₂ := eq762 (k X0 X0)
       grind)
    | exact superpose eq762 eq1171
    | exact resolve eq1171 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1177 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1174 X0
       have i₂ := eq762 X0
       grind)
    | exact superpose eq762 eq1174
    | exact resolve eq1174 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq1174
  have eq1536 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | exact superpose eq183 eq175
    | exact resolve eq175 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1539 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq183 eq177
    | exact resolve eq177 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1550 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1539 X0 X1
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq1539
    | exact resolve eq1539 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq1553 : (M.op (M.op x y) (k (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | (have i₁ := eq1536
       have i₂ := eq626 sF0
       grind)
    | exact superpose eq626 eq1536
    | exact resolve eq1536 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1729 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq188 eq174
    | exact resolve eq174 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1730 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq188 eq175
    | exact resolve eq175 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1749 : (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1730
       have i₂ := eq626 sF4
       grind)
    | exact superpose eq626 eq1730
    | exact resolve eq1730 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1750 : (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1729
       have i₂ := eq626 sF4
       grind)
    | exact superpose eq626 eq1729
    | exact resolve eq1729 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq1786 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1749 eq1750
    | exact resolve eq1750 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1843 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1749 eq630
    | exact resolve eq630 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq1930 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1955 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1957 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq175
    | exact resolve eq175 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq176
  have eq1980 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1957 X0 X1
       have i₂ := eq626 (M.op X0 X1)
       grind)
    | exact superpose eq626 eq1957
    | exact resolve eq1957 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq1982 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1955 X0 X1 X2 X3
       have i₂ := eq626 (M.op X0 X1)
       grind)
    | exact superpose eq626 eq1955
    | exact resolve eq1955 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2006 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (k X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1930 X0 X1 X2 X3 X4
       have i₂ := eq626 X4
       grind)
    | exact superpose eq626 eq1930
    | exact resolve eq1930 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq2055 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1980 X0 X1
       have i₂ := eq740 X0 X1
       grind)
    | exact superpose eq740 eq1980
    | exact resolve eq1980 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2057 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1982 X0 X1 X2 X3
       have i₂ := eq740 X0 X1
       grind)
    | exact superpose eq740 eq1982
    | exact resolve eq1982 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq2118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2057 X0 X1 X2 X3
       have i₂ := eq2055 X0 X1
       grind)
    | exact superpose eq2055 eq2057
    | exact resolve eq2057 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq2057
  have eq2720 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 (k X0 X0)) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq996 (k X0 X0) (M.op X1 (k X0 X0))
       have i₂ := eq632 X0 (k X0 X0) X1
       grind)
    | exact superpose eq632 eq996
    | exact resolve eq996 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2728 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq996 (k X0 X0) X0
       have i₂ := eq1177 X0
       grind)
    | exact superpose eq1177 eq996
    | exact resolve eq996 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2848 : ∀ X0 : G, (M.op (k X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1177 X0
       have i₂ := eq2728 X0
       grind)
    | exact superpose eq2728 eq1177
    | exact resolve eq1177 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2851 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1004 X0
       have i₂ := eq2728 X0
       grind)
    | exact superpose eq2728 eq1004
    | exact resolve eq1004 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 : G, (M.op (k X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq177 X0 (k X0 X0)
       have i₂ := eq2728 X0
       grind)
    | exact superpose eq2728 eq177
    | exact resolve eq177 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq2894 : ∀ X0 : G, (M.op (k X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq2857 X0
       have i₂ := eq626 (M.op sF3 (M.op sF4 X0))
       grind)
    | exact superpose eq626 eq2857
    | exact resolve eq2857 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2897 : ∀ X0 : G, (M.op (k X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq2894 X0
       have i₂ := eq740 sF3 (M.op sF4 X0)
       grind)
    | exact superpose eq740 eq2894
    | exact resolve eq2894 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq2899 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2848 eq2897
    | exact resolve eq2897 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848 eq2897
  have eq3018 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq630 eq2851
    | exact resolve eq2851 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq5930 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 X0)) (k X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq997 (k X0 X0) (M.op X1 (k X0 X0))
       have i₂ := eq632 X0 (k X0 X0) X1
       grind)
    | exact superpose eq632 eq997
    | exact resolve eq997 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5940 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq997 (k X0 X0) X0
       have i₂ := eq1177 X0
       grind)
    | exact superpose eq1177 eq997
    | exact resolve eq997 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq5973 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq5930 X0 x
       have i₂ := eq2720 X0 x
       grind)
    | exact superpose eq2720 eq5930
    | exact resolve eq5930 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720 eq5930
  have eq6638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq1078 eq611
    | exact resolve eq611 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6648 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6638
       have r₂ := eq27
       grind)
    | exact resolve eq6638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6638
  have eq6655 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6648 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6648
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6648
       grind)
    | exact resolve eq13 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6658 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6648 eq177
    | exact resolve eq177 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6666 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq6655
  have eq6674 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6658
       have i₂ := eq626 sF3
       grind)
    | exact superpose eq626 eq6658
    | exact resolve eq6658 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6658
  have eq6683 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6674
    | exact resolve eq6674 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq6690 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6666 eq1078
    | exact resolve eq1078 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq6693 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6666 eq90
    | exact resolve eq90 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq6666
  have eq6700 : y = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq6690
  have eq6704 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq6693
    | exact resolve eq6693 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693
  have eq6707 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq6704
    | exact resolve eq6704 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq6704
  have eq6713 : y ≠ y ∨ y = (k x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6700
       grind)
    | exact superpose eq6700 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq6700
       grind)
    | exact resolve eq13 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6716 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq6700
       grind)
    | exact superpose eq6700 eq177
    | exact resolve eq177 eq6700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700
  have eq6724 : y = (k x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq6713
  have eq6732 : (M.op x y) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6716
       have i₂ := eq626 y
       grind)
    | exact superpose eq626 eq6716
    | exact resolve eq6716 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6716
  have eq6741 : (M.op x y) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6732
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6732
    | exact resolve eq6732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6732
  have eq6749 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6707
       grind)
    | exact superpose eq6707 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq6707
       grind)
    | exact resolve eq13 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6752 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq6707
       grind)
    | exact superpose eq6707 eq177
    | exact resolve eq177 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6757 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq996 x y
       have i₂ := eq6707
       grind)
    | exact superpose eq6707 eq996
    | exact resolve eq996 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq6760 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq6749
  have eq6764 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6757
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6757
    | exact resolve eq6757 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6757
  have eq6768 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6752
       have i₂ := eq626 y
       grind)
    | exact superpose eq626 eq6752
    | exact resolve eq6752 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq6774 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1553 eq6764
    | exact resolve eq6764 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553 eq6764
  have eq6777 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6768
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6768
    | exact resolve eq6768 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6768
  have eq6784 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq6724
       grind)
    | exact superpose eq6724 eq35
    | exact resolve eq35 eq6724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6724
  have eq6793 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6784
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6784
    | exact resolve eq6784 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6784
  have eq6801 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6741
       grind)
    | exact superpose eq6741 eq40
    | exact resolve eq40 eq6741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6807 : ∀ X0 : G, y = (M.op X0 (M.op (k X0 X0) (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq643 X0 y
       have i₂ := eq6741
       grind)
    | exact superpose eq6741 eq643
    | exact resolve eq643 eq6741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6741
  have eq6862 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6801
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6801
    | exact resolve eq6801 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq6881 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq6862
    | exact resolve eq6862 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6862
  have eq6896 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq6760
       grind)
    | exact superpose eq6760 eq35
    | exact resolve eq35 eq6760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6760
  have eq6905 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6896
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6896
    | exact resolve eq6896 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq6913 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6777
       grind)
    | exact superpose eq6777 eq40
    | exact resolve eq40 eq6777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq6919 : ∀ X0 : G, y = (M.op X0 (M.op (k X0 X0) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq643 X0 y
       have i₂ := eq6777
       grind)
    | exact superpose eq6777 eq643
    | exact resolve eq643 eq6777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6974 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6913
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6913
    | exact resolve eq6913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6913
  have eq6993 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq6974
    | exact resolve eq6974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974
  have eq7009 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6793 eq611
    | exact resolve eq611 eq6793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6793
  have eq7017 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7009
  have eq7111 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6905 eq611
    | exact resolve eq611 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq6905
  have eq7119 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq7111
  have eq7139 : (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6993 eq642
    | exact resolve eq642 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7504 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6683 eq115
    | exact resolve eq115 eq6683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq6683
  have eq7590 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6707 eq7504
    | exact resolve eq7504 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504
  have eq7759 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6774 eq1177
    | exact resolve eq1177 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq6774
  have eq8329 : (M.op (σ y) (σ y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq7139 eq177
    | exact resolve eq177 eq7139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7139
  have eq8343 : (k (σ y) (σ y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8329
       have i₂ := eq626 sF3
       grind)
    | exact superpose eq626 eq8329
    | exact resolve eq8329 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq8349 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6993 eq8343
    | exact resolve eq8343 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8343
  have eq8807 : (M.op x y) = (M.op (M.op x y) (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq7590 eq642
    | exact resolve eq642 eq7590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq7590
  have eq8870 : (M.op x y) = (M.op (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8807
       have i₂ := eq405 sF4 sF4
       grind)
    | exact superpose eq405 eq8807
    | exact resolve eq8807 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq8807
  have eq9101 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7017 eq177
    | exact resolve eq177 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq9117 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9101
       have i₂ := eq626 sF3
       grind)
    | exact superpose eq626 eq9101
    | exact resolve eq9101 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9101
  have eq9126 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq9117
    | exact resolve eq9117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9117
  have eq9131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6881 eq9126
    | exact resolve eq9126 eq6881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9126
  have eq9132 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq9131
       have r₂ := eq27
       grind)
    | exact resolve eq9131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9131
  have eq9263 : ∀ X0 X1 : G, (M.op y X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op x y)) (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5973 (M.op (M.op x sF0) (k X0 X0))
       have i₂ := eq632 X0 sF0 x
       grind)
    | exact superpose eq632 eq5973
    | exact resolve eq5973 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9264 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (k (M.op x y) (M.op x y)) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5973 (M.op (k sF0 sF0) (k x x))
       have i₂ := eq643 sF0 x
       grind)
    | exact superpose eq643 eq5973
    | exact resolve eq5973 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9294 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op x y) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq5973 eq177
    | exact resolve eq177 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9307 : ∀ X0 : G, (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op x y) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq9294 X0
       have i₂ := eq626 (M.op sF3 (M.op sF4 X0))
       grind)
    | exact superpose eq626 eq9294
    | exact resolve eq9294 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9294
  have eq9327 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op x y) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq9307 X0
       have i₂ := eq740 sF3 (M.op sF4 X0)
       grind)
    | exact superpose eq740 eq9307
    | exact resolve eq9307 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9307
  have eq9339 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2899 eq9327
    | exact resolve eq9327 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899 eq9327
  have eq9346 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq7119 eq177
    | exact resolve eq177 eq7119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7119
  have eq9362 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9346
       have i₂ := eq626 sF3
       grind)
    | exact superpose eq626 eq9346
    | exact resolve eq9346 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9371 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9362
    | exact resolve eq9362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9362
  have eq9376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6993 eq9371
    | exact resolve eq9371 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993 eq9371
  have eq9377 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9376
       have r₂ := eq27
       grind)
    | exact resolve eq9376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9376
  have eq9378 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9377 eq27
    | exact resolve eq27 eq9377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9377
  have eq9984 : (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op x y)) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op x y)) (M.op (σ y) y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6807 eq2851
    | exact resolve eq2851 eq6807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851 eq6807
  have eq10000 : (M.op (k (σ y) (σ y)) (M.op x y)) = (M.op (M.op (k (σ y) (σ y)) (M.op x y)) (M.op (σ y) y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9132 eq9984
    | exact resolve eq9984 eq9132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132 eq9984
  have eq10030 : (M.op (σ (M.op x y)) (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op x y)) (M.op (σ y) y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6881 eq10000
    | exact resolve eq10000 eq6881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6881 eq10000
  have eq17315 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (k X0 X0)) = (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op x y)) (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9339 (M.op (M.op x sF0) (k X0 X0))
       have i₂ := eq632 X0 sF0 x
       grind)
    | exact superpose eq632 eq9339
    | exact resolve eq9339 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17319 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) = (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (k (M.op x y) (M.op x y)) (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9339 (M.op (k sF0 sF0) (k x x))
       have i₂ := eq643 sF0 x
       grind)
    | exact superpose eq643 eq9339
    | exact resolve eq9339 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq9339
  have eq17446 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq9264 eq17319
    | exact resolve eq17319 eq9264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9264 eq17319
  have eq17450 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (k X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq9263 eq17315
    | exact resolve eq17315 eq9263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9263 eq17315
  have eq21706 : ∀ X0 : G, (M.op (M.op (σ y) y) (M.op (M.op (σ (M.op x y)) (M.op x y)) (k X0 X0))) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq10030 eq632
    | exact resolve eq632 eq10030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10030
  have eq21720 : ∀ X0 : G, (M.op (M.op (σ y) y) (M.op X0 (M.op y X0))) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq17450 eq21706
    | exact resolve eq21706 eq17450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21706
  have eq22874 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq998 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq998 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq998 eq998
    | exact resolve eq998 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq33840 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq188 eq2118
    | exact resolve eq2118 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq34015 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq33840 X0 X1
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq33840
    | exact resolve eq33840 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33840
  have eq34297 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34015 X0 X1
       have i₂ := eq626 X1
       grind)
    | exact superpose eq626 eq34015
    | exact resolve eq34015 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34015
  have eq40648 : x = (M.op (M.op (σ y) y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21720 x
       have i₂ := eq6707
       grind)
    | exact superpose eq6707 eq21720
    | exact resolve eq21720 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6707
  have eq40664 : (M.op (k y y) (M.op x y)) = (M.op (M.op (σ y) y) (M.op (M.op (k y y) (M.op x y)) y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6919 eq21720
    | exact resolve eq21720 eq6919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919 eq21720
  have eq40732 : (M.op (k y y) (M.op x y)) = (M.op (M.op (σ y) y) (M.op (M.op (k y y) (M.op x y)) y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq40664
  have eq40736 : x = (M.op (M.op (σ y) y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq40648
  have eq40767 : (M.op (k y y) (M.op x y)) = (M.op (M.op (σ y) y) (M.op (M.op (k y y) (M.op x y)) y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq40732
       have r₂ := eq9378
       grind)
    | exact resolve eq40732 eq9378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40732
  have eq40782 : x = (M.op (M.op (σ y) y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq40736
       have r₂ := eq9378
       grind)
    | exact resolve eq40736 eq9378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9378 eq40736
  have eq40813 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ y) y) (M.op (M.op (M.op x y) (M.op x y)) y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6777 eq40767
    | exact resolve eq40767 eq6777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777 eq40767
  have eq40822 : x = (M.op (M.op (σ y) y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40782
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40782
    | exact resolve eq40782 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40782
  have eq40836 : (k (M.op x y) (M.op x y)) = (M.op (M.op (σ y) y) (M.op (k (M.op x y) (M.op x y)) y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40813
       have i₂ := eq626 sF0
       grind)
    | exact superpose eq626 eq40813
    | exact resolve eq40813 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40813
  have eq40843 : (k (M.op x y) (M.op x y)) = (M.op (M.op (σ y) y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7759 eq40836
    | exact resolve eq40836 eq7759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7759 eq40836
  have eq40848 : x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40822 eq40843
    | exact resolve eq40843 eq40822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40822 eq40843
  have eq42527 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40848 eq41
    | exact resolve eq41 eq40848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq40848
  have eq42747 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq42527
    | exact resolve eq42527 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42527
  have eq42795 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42747
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42747
    | exact resolve eq42747 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42747
  have eq43412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42795 eq8349
    | exact resolve eq8349 eq42795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349 eq42795
  have eq43613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq43412
  have eq43689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq43613
    | exact resolve eq43613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43613
  have eq43745 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43689
       have r₂ := eq27
       grind)
    | exact resolve eq43689 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43689
  have eq43777 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq43745 eq31
    | exact resolve eq31 eq43745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43886 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq43777
    | exact resolve eq43777 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43777
  have eq43887 : y = (M.op x y) ∨ x = y := by grind
  clear eq43886
  have eq43895 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq18
    | exact resolve eq18 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43906 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (k X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq631 X0
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq631
    | exact resolve eq631 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq43918 : (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq1786
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq1786
    | exact resolve eq1786 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq43925 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5940 X0
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq5940
    | exact resolve eq5940 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5940
  have eq43926 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5973 X0
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq5973
    | exact resolve eq5973 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43997 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq44534 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (k X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq43906 eq5973
    | exact resolve eq5973 eq43906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973
  have eq44596 : ∀ X0 : G, (M.op y X0) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34297 eq44534
    | exact resolve eq44534 eq34297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44534
  have eq44606 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq43887 eq44596
    | exact resolve eq44596 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44596
  have eq44787 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (k (M.op x y) (M.op x y)))) (M.op (k (M.op x y) (M.op x y)) (M.op X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq44606 eq183
    | exact resolve eq183 eq44606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44606
  have eq45051 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (k (M.op x y) (M.op x y)))) (M.op (k (M.op x y) (M.op x y)) (k X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44787 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq44787
    | exact resolve eq44787 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44787
  have eq45082 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (k (M.op x y) (M.op x y)))) (M.op X0 (M.op y X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq17446 eq45051
    | exact resolve eq45051 eq17446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17446 eq45051
  have eq45094 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq45082 X0
       have i₂ := eq1004 sF0
       grind)
    | exact superpose eq1004 eq45082
    | exact resolve eq45082 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45082
  have eq45100 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq43887 eq45094
    | exact resolve eq45094 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45094
  have eq45137 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (k X0 X0)) = (M.op (M.op x y) (M.op (M.op (M.op X1 (M.op x y)) (k X0 X0)) X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq45100 (M.op (M.op x sF0) (k X0 X0))
       have i₂ := eq632 X0 sF0 x
       grind)
    | exact superpose eq632 eq45100
    | exact resolve eq45100 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45169 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op X1 X2) (k (M.op x y) (M.op x y))) X0) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq45100 eq2006
    | exact resolve eq2006 eq45100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006 eq45100
  have eq45257 : ∀ X0 X1 : G, (M.op (M.op x y) (k X0 X0)) = (M.op (M.op X1 (M.op x y)) (k X0 X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq45137 X0 X1
       have i₂ := eq1550 X0 (M.op X1 sF0)
       grind)
    | exact superpose eq1550 eq45137
    | exact resolve eq45137 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq45137
  have eq45275 : ∀ X0 : G, (M.op (M.op x y) (k X0 X0)) = (M.op X0 (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17450 eq45257
    | exact resolve eq45257 eq17450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17450 eq45257
  have eq45283 : ∀ X0 : G, (M.op (M.op x y) (k X0 X0)) = (M.op X0 (M.op (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq43887 eq45275
    | exact resolve eq45275 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45275
  have eq49532 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq43918 eq1843
    | exact resolve eq1843 eq43918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq43918
  have eq49709 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq49532 eq632
    | exact resolve eq632 eq49532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49532
  have eq49953 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1004 X0
       have i₂ := eq43925 X0
       grind)
    | exact superpose eq43925 eq1004
    | exact resolve eq1004 eq43925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq50004 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq632 (M.op X0 X1) X1 X0
       have i₂ := eq43925 (M.op X0 X1)
       grind)
    | exact superpose eq43925 eq632
    | exact resolve eq632 eq43925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43925
  have eq50999 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (k X0 X0)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq43926 (M.op (M.op x sF4) (k X0 X0))
       have i₂ := eq632 X0 sF4 x
       grind)
    | exact superpose eq632 eq43926
    | exact resolve eq43926 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51106 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f51106_13 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
      intro X0 X1
      grind
    have f51106_14 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ y = x := by
      intro X0
      grind
    have f51106_23 : (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) ≠ (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) := by grind
    have f51106_24 : y ≠ x := by grind
    have f51106_27 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
      intro X0
      first
      | (have j0 := f51106_14 X0
         grind)
      | (have r₁ := f51106_14 X0
         have r₂ := f51106_24
         grind)
      | exact resolve f51106_14 f51106_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f51106_96 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) := by
      intro X0
      first
      | (have i₁ := f51106_13 (σ y) (M.op (M.op (σ x) (σ y)) X0)
         have i₂ := f51106_27 X0
         grind)
      | exact superpose f51106_27 f51106_13
      | exact resolve f51106_13 f51106_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f51106_99 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) := by
      intro X0
      first
      | (have i₁ := f51106_96 X0
         have i₂ := f51106_13 (M.op x y) (M.op (M.op x y) X0)
         grind)
      | exact superpose f51106_13 f51106_96
      | exact resolve f51106_96 f51106_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f51106_119 : (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) ≠ (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) := by
      first
      | (have i₁ := f51106_23
         have i₂ := f51106_13 (M.op x y) (M.op (M.op x y) X0)
         grind)
      | exact superpose f51106_13 f51106_23
      | exact resolve f51106_23 f51106_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f51106_120 : False := by
      first
      | (have r₁ := f51106_119
         have r₂ := f51106_99 X0
         grind)
      | exact resolve f51106_119 f51106_99
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f51106_120
  clear eq43926
  have eq51204 : ∀ X0 : G, (k (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51106 X0
       have i₂ := eq626 (M.op sF0 (M.op sF0 X0))
       grind)
    | exact superpose eq626 eq51106
    | exact resolve eq51106 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51106
  have eq51256 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51204 X0
       have i₂ := eq740 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq740 eq51204
    | exact resolve eq51204 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq51204
  have eq51282 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51256 x
       have i₂ := eq22874 sF0 sF0 x
       grind)
    | exact superpose eq22874 eq51256
    | exact resolve eq51256 eq22874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22874 eq51256
  have eq51297 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq49953 eq51282
    | exact resolve eq51282 eq49953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49953 eq51282
  have eq52639 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (k X0 X0)) = (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (k X0 X0))))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq51297 (M.op (M.op x sF4) (k X0 X0))
       have i₂ := eq632 X0 sF4 x
       grind)
    | exact superpose eq632 eq51297
    | exact resolve eq51297 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51297
  have eq52853 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (k X0 X0)) = (M.op X0 (M.op (σ y) X0)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq50999 eq52639
    | exact resolve eq52639 eq50999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50999 eq52639
  have eq63363 : ∀ X0 : G, (M.op (M.op x y) (k X0 X0)) = (M.op (k X0 X0) (M.op (M.op x y) X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq43906 eq50004
    | exact resolve eq50004 eq43906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50004
  have eq63551 : ∀ X0 : G, (M.op (M.op x y) (k X0 X0)) = (M.op (k X0 X0) (M.op (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq63363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63363
  have eq65669 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (k X0 X0)))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq49709 eq2118
    | exact resolve eq2118 eq49709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq49709
  have eq65758 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34297 eq65669
    | exact resolve eq65669 eq34297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34297 eq65669
  have eq65867 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op (σ x) (σ y))))) (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq65758 eq183
    | exact resolve eq183 eq65758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq65758
  have eq66191 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op (σ x) (σ y))))) (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (k X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq65867 X0
       have i₂ := eq626 X0
       grind)
    | exact superpose eq626 eq65867
    | exact resolve eq65867 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65867
  have eq66260 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op (σ x) (σ y))))) (M.op X0 (M.op (σ y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq52853 eq66191
    | exact resolve eq66191 eq52853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52853 eq66191
  have eq66308 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) (M.op X0 (M.op (σ y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq63551 eq66260
    | exact resolve eq66260 eq63551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63551 eq66260
  have eq66343 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq43906 eq66308
    | exact resolve eq66308 eq43906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43906 eq66308
  have eq66492 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq6648 eq66343
    | exact resolve eq66343 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648 eq66343
  have eq66632 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq66492
  have eq66738 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq66632
    | exact resolve eq66632 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66632
  have eq66772 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq66738
       have i₂ := eq626 sF4
       grind)
    | exact superpose eq626 eq66738
    | exact resolve eq66738 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66738
  have eq66790 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq43887 eq66772
    | exact resolve eq66772 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43887 eq66772
  have eq82633 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op (M.op x y) (k X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq45169 eq632
    | exact resolve eq632 eq45169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq45169
  have eq84177 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (M.op x y) X0))) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq45283 eq82633
    | exact resolve eq82633 eq45283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45283 eq82633
  have eq84265 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (M.op x y) X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq84177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84177
  have eq194812 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq66790 eq8870
    | exact resolve eq8870 eq66790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8870 eq66790
  have eq195127 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq194812
  have eq195255 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq29 eq195127
    | exact resolve eq195127 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195127
  have eq195256 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq195255
  have eq195323 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq43745 eq195256
    | exact resolve eq195256 eq43745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43745 eq195256
  have eq195324 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq195323
  have eq195420 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq195324 eq84265
    | exact resolve eq84265 eq195324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84265
  have eq195437 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq195324 eq177
    | exact resolve eq177 eq195324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq195324
  have eq195535 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq195420
  have eq195600 : (k (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq195437
       have i₂ := eq626 sF0
       grind)
    | exact superpose eq626 eq195437
    | exact resolve eq195437 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195437
  have eq195609 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43895 eq195535
    | exact resolve eq195535 eq43895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195535
  have eq195661 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43895 eq195600
    | exact resolve eq195600 eq43895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43895 eq195600
  have eq195667 : x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq195609
       have i₂ := eq3018 sF0
       grind)
    | exact superpose eq3018 eq195609
    | exact resolve eq195609 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq195609
  have eq195703 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq195661 eq195667
    | exact resolve eq195667 eq195661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195661 eq195667
  have eq195729 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq195703
       have r₂ := eq43997
       grind)
    | exact resolve eq195703 eq43997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43997 eq195703
  have eq195744 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq195729 eq31
    | exact resolve eq31 eq195729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq195729
  have eq196060 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq195744
    | exact resolve eq195744 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq195744
  have eq196061 : x = y := by grind
  clear eq196060
  have eq196126 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq196061
       grind)
    | exact superpose eq196061 eq18
    | exact resolve eq18 eq196061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq196127 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq196061
       grind)
    | exact superpose eq196061 eq24
    | exact resolve eq24 eq196061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq196061
  have eq196181 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq196127
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196127
    | exact resolve eq196127 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196127
  have eq196182 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq196126
       have i₂ := eq626 x
       grind)
    | exact superpose eq626 eq196126
    | exact resolve eq196126 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196126
  have eq196187 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq196181 eq26
    | exact resolve eq26 eq196181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq196181
  have eq196384 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq196187
       have i₂ := eq626 sF2
       grind)
    | exact superpose eq626 eq196187
    | exact resolve eq196187 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq196187
  have eq196426 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq196182
       grind)
    | exact superpose eq196182 eq39
    | exact resolve eq39 eq196182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq196182
  have eq196627 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq196426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196426
    | exact resolve eq196426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq196426
  have eq196651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq196384 eq196627
    | exact resolve eq196627 eq196384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196384 eq196627
  have eq196661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq196651
    | exact resolve eq196651 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq196651
  have eq196668 : False := by grind
  exact eq196668

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | (have j1 := eq24 (τ X0)
       grind)
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | (have j0 := eq84 X0
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | (have j0 := eq88 X0
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq92 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq92 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq26
    | (have j0 := eq26 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq96 (σ X0)
       grind)
    | exact superpose eq96 eq15
    | exact resolve eq15 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq122
    | exact resolve eq122 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq122
  have eq2067 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 x y
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq101 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq101 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq101 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq2092 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2067
  have eq2131 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2092
       grind)
    | exact superpose eq2092 eq16
    | exact resolve eq16 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2133 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2092
       grind)
    | exact superpose eq2092 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2092
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2092
       grind)
    | exact resolve eq12 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2147 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2133
  have eq2156 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2147
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2147
    | exact resolve eq2147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq4608 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2156
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2156
    | (have j1 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq2156 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq4638 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq4608
  have eq4651 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4638
       have r₂ := eq2131
       grind)
    | exact resolve eq4638 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq4638
  have eq8141 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4651
       grind)
    | exact superpose eq4651 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq4651
       grind)
    | exact resolve eq12 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8169 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8141
  have eq10631 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26 x y
       have i₂ := eq8169
       grind)
    | exact superpose eq8169 eq26
    | (have j0 := eq26 x y
       grind)
    | exact resolve eq26 eq8169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8169
  have eq10634 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10631
  have eq25194 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq10634
       grind)
    | exact superpose eq10634 eq16
    | exact resolve eq16 eq10634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10634
  have eq33927 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25194
       have i₂ := eq4651
       grind)
    | exact superpose eq4651 eq25194
    | exact resolve eq25194 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4651 eq25194
  have eq33928 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33927
  have eq33929 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq33928
  have eq40902 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq33929
       grind)
    | exact superpose eq33929 eq10
    | exact resolve eq10 eq33929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33929
  have eq40983 : x = y ∨ x = y := by
    first
    | (have i₁ := eq40902
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40902
    | exact resolve eq40902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40902
  have eq40984 : x = y := by grind
  clear eq40983
  have eq52912 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40984
       grind)
    | exact superpose eq40984 eq16
    | exact resolve eq16 eq40984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40984
  have eq52913 : False := by grind
  exact eq52913

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq53
    | exact resolve eq53 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq112 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq141 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq152 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq112
    | exact resolve eq112 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq247 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq167 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq167
    | exact resolve eq167 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq329 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X2
       have i₂ := eq168 X2 X0 X1
       grind)
    | exact superpose eq168 eq73
    | exact resolve eq73 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq332 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq175 X2 X3
       have i₂ := eq168 X2 X0 X1
       grind)
    | exact superpose eq168 eq175
    | exact resolve eq175 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq168 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq168 eq9
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op X2 (M.op (M.op X3 X2) (M.op (σ X0) (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X0) X2 X3
       have i₂ := eq141 X0 X1
       grind)
    | (have i₁ := eq9 (σ X1) X1 X2
       have i₂ := eq141 X1 X1
       grind)
    | exact superpose eq141 eq9
    | (have j1 := eq141 X0 X1
       grind)
    | exact resolve eq9 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq141 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq141 X0 X1
       grind)
    | exact superpose eq141 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq141 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq141 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq141 X1 X1
       grind)
    | exact resolve eq13 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq545 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq538 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq546 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq545 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq549 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1435 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X0 (M.op X1 X0) X2 X3
       have i₂ := eq168 X0 X0 X1
       grind)
    | exact superpose eq168 eq71
    | exact resolve eq71 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1435 X0 X1 x x
       have i₂ := eq71 X0 X0 x x
       grind)
    | exact superpose eq71 eq1435
    | exact resolve eq1435 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1935 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq152 X2 X3
       have i₂ := eq168 X2 X0 X1
       grind)
    | exact superpose eq168 eq152
    | exact resolve eq152 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq168
  have eq2907 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq247 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq332 X1 X2 X0 X4
       grind)
    | exact superpose eq332 eq247
    | exact resolve eq247 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3124 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2907 X0 X1 X2 X3 X4
       have i₂ := eq53 X4 X0
       grind)
    | exact superpose eq53 eq2907
    | exact resolve eq2907 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2907
  have eq3199 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3124 X0 X1 X2 X3 X4
       have i₂ := eq53 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq53 eq3124
    | exact resolve eq3124 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3233 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3199 X0 X1 X2 X3 X4
       have i₂ := eq332 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq332 eq3199
    | exact resolve eq3199 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3199
  have eq3242 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3233 X0 x x X3 X4
       have i₂ := eq329 x x X0
       grind)
    | exact superpose eq329 eq3233
    | exact resolve eq3233 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq3233
  have eq3273 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3242 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq247 X0 x X1
       grind)
    | exact superpose eq247 eq3242
    | exact resolve eq3242 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq3242
  have eq3365 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3273 X0 X1 X2
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq3273
    | exact resolve eq3273 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq3273
  have eq3388 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3365 X0 X1 X2
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq3365
    | exact resolve eq3365 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq6864 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq167 X1 x X0
       grind)
    | exact superpose eq167 eq345
    | exact resolve eq345 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq6874 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq345 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq345
    | exact resolve eq345 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7046 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6874 X0 X1 X2 X3
       have i₂ := eq3388 X0 X3 X0
       grind)
    | exact superpose eq3388 eq6874
    | exact resolve eq6874 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874
  have eq7053 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6864 X0 X1
       have i₂ := eq3388 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq3388 eq6864
    | exact resolve eq6864 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388 eq6864
  have eq7515 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq7053 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq7053 eq332
    | exact resolve eq332 eq7053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq7053
  have eq7556 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7515 X0 X1 X2
       have i₂ := eq53 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq53 eq7515
    | exact resolve eq7515 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7515
  have eq9892 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 (τ X0) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq549
    | (have j0 := eq549 (τ X0) X1
       grind)
    | exact resolve eq549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq10056 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9892 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9892
    | (have j0 := eq9892 X0 X1
       grind)
    | exact resolve eq9892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9892
  have eq10074 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10056 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10056
    | (have j0 := eq10056 X0 X1
       grind)
    | exact resolve eq10056 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10056
  have eq10706 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3)))) = X0 ∨ (σ (k (τ X0) X3)) = (M.op (σ X3) X0) ∨ (M.op (σ X3) (σ X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq519 (τ X0) X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq519
    | exact resolve eq519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq10936 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3)))) = X0 ∨ (M.op (σ X3) X0) = (k X0 (σ X3)) ∨ (M.op (σ X3) (σ X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10706 X0 X1 X2 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq10706
    | (have j0 := eq10706 X0 X1 X2 X3
       grind)
    | exact resolve eq10706 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10706
  have eq30196 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7556 X1 x (M.op X0 X0)
       have i₂ := eq7046 X0 x X1 X1
       grind)
    | exact superpose eq7046 eq7556
    | exact resolve eq7556 eq7046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046 eq7556
  have eq70158 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) ≠ (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq10074 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10074
  have eq76539 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) X0)) = (M.op (M.op X1 (M.op X0 (σ X2))) (M.op X0 (σ X2))) ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq71 (M.op X0 (σ X2)) (M.op X1 (M.op X0 (σ X2))) X3 X4
       have i₂ := eq10936 X0 (M.op X0 (σ X2)) X1 X2
       grind)
    | exact superpose eq10936 eq71
    | (have j1 := eq10936 X0 X1 X2 X2
       grind)
    | exact resolve eq71 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq10936
  have eq76920 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) X0)) = (M.op (M.op X0 (σ X2)) (M.op X0 (σ X2))) ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq76539 X0 x X2 X3 X4
       have i₂ := eq1520 (M.op X0 (σ X2)) x
       grind)
    | exact superpose eq1520 eq76539
    | (have j0 := eq76539 X0 x X2 X3 X4
       grind)
    | exact resolve eq76539 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520 eq76539
  have eq77074 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) X0)) = (M.op (σ X2) (M.op X0 (σ X2))) ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq76920 X0 X2 X3 X4
       have i₂ := eq53 X0 (σ X2)
       grind)
    | exact superpose eq53 eq76920
    | (have j0 := eq76920 X0 X2 X3 X4
       grind)
    | exact resolve eq76920 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq76920
  have eq174231 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X2 (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq345 (M.op X3 X3) X3 X3 X2
       have i₂ := eq1935 X0 X1 X2 X3
       grind)
    | exact superpose eq1935 eq345
    | exact resolve eq345 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq1935
  have eq2605455 : ∀ X0 X1 X2 X3 : G, (M.op (σ X3) (σ X3)) = (M.op X2 (M.op (M.op (σ X3) (σ X3)) (M.op X0 (M.op (M.op X1 X0) X2)))) ∨ (k X2 (σ X3)) = (M.op (σ X3) X2) ∨ (M.op (σ X3) (σ X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30196 (σ X3) X2
       have i₂ := eq77074 X2 X3 X0 X1
       grind)
    | exact superpose eq77074 eq30196
    | (have j1 := eq77074 X2 X3 X3 x
       grind)
    | exact resolve eq30196 eq77074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30196 eq77074
  have eq2606757 : ∀ X2 X3 : G, (M.op (σ X3) (σ X3)) = (M.op (σ X3) X2) ∨ (k X2 (σ X3)) = (M.op (σ X3) X2) ∨ (M.op (σ X3) (σ X3)) = X2 := by
    intro X2 X3
    first
    | (have i₁ := eq2605455 x x X2 X3
       have i₂ := eq174231 x x X2 (σ X3)
       grind)
    | exact superpose eq174231 eq2605455
    | (have j0 := eq2605455 x x X2 X3
       grind)
    | exact resolve eq2605455 eq174231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174231 eq2605455
  have eq2609010 : ∀ X2 X3 : G, (k X2 (σ X3)) = (M.op (σ X3) X2) ∨ (M.op (σ X3) (σ X3)) = X2 := by
    intro X2 X3
    first
    | (have j0 := eq2606757 X2 X3
       have j1 := eq70158 X2 X3
       grind)
    | (have r₁ := eq2606757 x x
       have r₂ := eq70158 x x
       grind)
    | (have r₁ := eq2606757 (σ x) x
       have r₂ := eq70158 (σ x) x
       grind)
    | (have r₁ := eq2606757 (M.op (σ x) x) x
       have r₂ := eq70158 x x
       grind)
    | exact resolve eq2606757 eq70158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70158 eq2606757
  have eq2610787 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2609010 x (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2609010
    | exact resolve eq2609010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2611032 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2609010 (σ X0) X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2609010
    | (have j0 := eq2609010 (σ X0) X1
       grind)
    | exact resolve eq2609010 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609010
  have eq2614505 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq2610787 X0 (τ X1)
       grind)
    | exact superpose eq2610787 eq18
    | (have j1 := eq2610787 X0 (τ X1)
       grind)
    | exact resolve eq18 eq2610787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2617856 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2614505 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2614505
    | exact resolve eq2614505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614505
  have eq2619664 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2617856 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2617856
    | (have j0 := eq2617856 X0 X1
       grind)
    | exact resolve eq2617856 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617856
  have eq2778968 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2611032 y x
       grind)
    | exact superpose eq2611032 eq16
    | (have j1 := eq2611032 y x
       grind)
    | exact resolve eq16 eq2611032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611032
  have eq2780377 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2778968
       have i₂ := eq2610787 x y
       grind)
    | exact superpose eq2610787 eq2778968
    | (have j1 := eq2610787 (σ x) (σ y)
       grind)
    | exact resolve eq2778968 eq2610787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610787
  have eq2780386 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2780377
  have eq2780639 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2780386
  have eq2781741 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2780639
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2780639
    | exact resolve eq2780639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780639
  have eq2784855 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2781741
       grind)
    | exact superpose eq2781741 eq16
    | exact resolve eq16 eq2781741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781741
  have eq2785602 : y = (M.op x x) := by
    first
    | (have j1 := eq2619664 y x
       grind)
    | (have r₁ := eq2784855
       have r₂ := eq2619664 y x
       grind)
    | exact resolve eq2784855 eq2619664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619664 eq2784855
  have eq2785634 : (M.op x y) = (k y x) := by grind
  clear eq2785602
  have eq2787568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2778968
       have i₂ := eq2785634
       grind)
    | exact superpose eq2785634 eq2778968
    | exact resolve eq2778968 eq2785634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778968
  have eq2787617 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2787568
  have eq2898067 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq2787617
  have eq2899159 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq2898067
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2898067
    | exact resolve eq2898067 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898067
  have eq2899335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2899159
       have i₂ := eq2785634
       grind)
    | exact superpose eq2785634 eq2899159
    | exact resolve eq2899159 eq2785634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785634 eq2899159
  have eq2899382 : False := by grind
  exact eq2899382

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    grind
  have eq70 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq23
    | exact resolve eq23 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq70
    | exact resolve eq70 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq125 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq96
    | exact resolve eq96 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq71 (M.op x (M.op x x))
       have i₂ := eq96 x x
       grind)
    | exact superpose eq96 eq71
    | exact resolve eq71 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq96 X1 X1
       grind)
    | exact superpose eq96 eq97
    | exact resolve eq97 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq135
    | exact resolve eq135 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq205 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq134 X2 X3 X4
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq134
    | exact resolve eq134 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X1 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X2 X2))
       have i₂ := eq96 X2 X0
       grind)
    | exact superpose eq96 eq134
    | exact resolve eq134 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq220 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq138 X2 X3
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq138
    | exact resolve eq138 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X2
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq75
    | exact resolve eq75 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq134 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq134 eq9
    | exact resolve eq9 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 X2 X3 X2
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq140
    | exact resolve eq140 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq837 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq819 X2 X3 X4
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq819
    | exact resolve eq819 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq819 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq9 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X0
       grind)
    | exact superpose eq9 eq819
    | exact resolve eq819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq890 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq840 X0 X1 X2
       have i₂ := eq63 X0 (M.op X1 X2)
       grind)
    | exact superpose eq63 eq840
    | exact resolve eq840 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq967 : ∀ X0 X1 : G, (k (σ X1) (k (σ (M.op (τ X0) (τ X0))) X0)) = (σ (k X1 (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (M.op (τ X0) (τ X0)) X0 X1
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq27
    | exact resolve eq27 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1067 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 X0 (M.op X1 X0) X2 X3
       have i₂ := eq134 X0 X0 X1
       grind)
    | exact superpose eq134 eq77
    | exact resolve eq77 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1067 X0 X1 x x
       have i₂ := eq77 X0 X0 x x
       grind)
    | exact superpose eq77 eq1067
    | exact resolve eq1067 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X1 (M.op X2 X0) (M.op X2 (M.op X2 X2))
       have i₂ := eq125 X0 X2
       grind)
    | exact superpose eq125 eq134
    | exact resolve eq134 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223 (M.op X2 X0) (M.op X2 (M.op X2 X2)) X1
       have i₂ := eq125 X0 X2
       grind)
    | exact superpose eq125 eq223
    | exact resolve eq223 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq1592 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq205 X0 X1 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq205
    | exact resolve eq205 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1810 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211 (M.op X2 X0) (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq138 X0 X2
       grind)
    | exact superpose eq138 eq211
    | exact resolve eq211 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1952 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1810 X0 X1 X2
       have i₂ := eq63 X2 X0
       grind)
    | exact superpose eq63 eq1810
    | exact resolve eq1810 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1992 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1952 X0 X1 X2
       have i₂ := eq63 X0 (M.op X0 X0)
       grind)
    | exact superpose eq63 eq1952
    | exact resolve eq1952 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2008 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1992 X0 X1 X2
       have i₂ := eq138 X0 X0
       grind)
    | exact superpose eq138 eq1992
    | exact resolve eq1992 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2013 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2008 X0 X1 X2
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq2008
    | exact resolve eq2008 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2008
  have eq2163 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2013 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq211 X1 X0 x
       grind)
    | exact superpose eq211 eq2013
    | exact resolve eq2013 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2236 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2163 X0 X1 X2
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq2163
    | exact resolve eq2163 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2253 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2236 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2236
    | exact resolve eq2236 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2236
  have eq3183 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq140 X1 x X0
       grind)
    | exact superpose eq140 eq229
    | exact resolve eq229 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq3185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq229 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq229
    | exact resolve eq229 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3206 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq229 X0 X2 (M.op X1 (M.op X2 X0)) X0
       have i₂ := eq223 (M.op X2 X0) X1 X0
       grind)
    | exact superpose eq223 eq229
    | exact resolve eq229 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3207 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq229 X1 X3 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       have i₂ := eq229 (M.op X3 X1) X2 X0 X1
       grind)
    | exact superpose eq229 eq229
    | exact resolve eq229 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq3278 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3207 X0 X1 X2 X3
       have i₂ := eq2253 X1 X0 X0
       grind)
    | exact superpose eq2253 eq3207
    | exact resolve eq3207 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq3292 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3185 X0 X1 X2 X3
       have i₂ := eq2253 X0 X3 X0
       grind)
    | exact superpose eq2253 eq3185
    | exact resolve eq3185 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3293 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3183 X0 X1
       have i₂ := eq2253 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2253 eq3183
    | exact resolve eq3183 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183
  have eq3474 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3293 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq211 X1 X0 (M.op X1 X1)
       grind)
    | exact superpose eq211 eq3293
    | exact resolve eq3293 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq3555 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq3293 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq3293 eq220
    | exact resolve eq220 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3581 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3555 X0 X1 X2
       have i₂ := eq2253 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2253 eq3555
    | exact resolve eq3555 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq3617 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3474 X0 X1
       have i₂ := eq2253 X0 X1 X1
       grind)
    | exact superpose eq2253 eq3474
    | exact resolve eq3474 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3650 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3617 X0 X1
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq3617
    | exact resolve eq3617 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq3617
  have eq3715 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3650 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq220 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq220 eq3650
    | exact resolve eq3650 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3889 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3715 X2 X1 X0
       have i₂ := eq3715 X2 X1 X3
       grind)
    | (have i₁ := eq3715 X0 X1 X2
       have i₂ := eq3715 X0 X1 X1
       grind)
    | exact superpose eq3715 eq3715
    | exact resolve eq3715 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3897 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3715 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq3650 X0 X2
       grind)
    | exact superpose eq3650 eq3715
    | exact resolve eq3715 eq3650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650
  have eq4025 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3293 X2 X1
       have i₂ := eq3715 X2 X1 X0
       grind)
    | (have i₁ := eq3293 X0 X1
       have i₂ := eq3715 X0 X1 X1
       grind)
    | exact superpose eq3715 eq3293
    | exact resolve eq3293 eq3715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq3715
  have eq5094 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3581 X1 X3 (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0)
       have i₂ := eq220 (M.op X3 (M.op X1 X1)) X2 X0 (M.op X2 (M.op X3 (M.op X1 X1)))
       grind)
    | exact superpose eq220 eq3581
    | exact resolve eq3581 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5142 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq3581 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq3581 eq77
    | exact resolve eq77 eq3581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581
  have eq5167 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5142 X0 X1 X2 X3
       have i₂ := eq2253 X3 X2 X2
       grind)
    | exact superpose eq2253 eq5142
    | exact resolve eq5142 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq6992 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op X2 X2) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X1) X2
       have i₂ := eq177 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 (σ X1) X2
       have j1 := eq177 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq177 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq177 X0 X1
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7065 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op (σ X0) (σ X0)) (M.op X2 X2))) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X1)
       have i₂ := eq177 X0 X1
       grind)
    | (have i₁ := eq9 X0 (σ X0) (σ X0)
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq9
    | (have j1 := eq177 X0 X1
       grind)
    | exact resolve eq9 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8137 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5094 X2 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3 X4
       have i₂ := eq300 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq300 eq5094
    | exact resolve eq5094 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq5094
  have eq8182 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8137 X0 X1 X2 X3 X4
       have i₂ := eq2253 X1 X0 X0
       grind)
    | exact superpose eq2253 eq8137
    | exact resolve eq8137 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8137
  have eq8260 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8182 X0 X1 X2 X3 X4
       have i₂ := eq5167 X2 X1 X0 X1
       grind)
    | exact superpose eq5167 eq8182
    | exact resolve eq8182 eq5167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167 eq8182
  have eq9878 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X3 X3))) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X3 (M.op X3 X3))) (M.op X1 (M.op X0 X1))) (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1459 X3 (M.op (M.op X2 (M.op X3 (M.op X3 X3))) (M.op X1 (M.op X0 X1))) X4
       have i₂ := eq77 X1 X0 (M.op X3 (M.op X3 X3)) X2
       grind)
    | exact superpose eq77 eq1459
    | exact resolve eq1459 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq10060 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X3 X3))) (M.op X1 (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9878 X0 X1 X2 X3 X4
       have i₂ := eq8260 X0 X1 (M.op (M.op X4 X3) (M.op X0 X1)) (M.op X2 (M.op X3 (M.op X3 X3))) X1
       grind)
    | exact superpose eq8260 eq9878
    | exact resolve eq9878 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9878
  have eq10136 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X1 (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq10060 X0 X1 x X3 X4
       have i₂ := eq8260 X3 X3 (M.op X1 (M.op X0 X1)) x X3
       grind)
    | exact superpose eq8260 eq10060
    | exact resolve eq10060 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060
  have eq30441 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (M.op (σ X0) (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7065 X0 X1 (M.op (σ X0) (σ X0))
       have i₂ := eq890 (M.op (σ X0) (σ X0)) (σ X0) (σ X0)
       grind)
    | exact superpose eq890 eq7065
    | (have j0 := eq7065 X0 X1 x
       grind)
    | exact resolve eq7065 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7065
  have eq30590 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30441 X0 X1
       have i₂ := eq9 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq9 eq30441
    | (have j0 := eq30441 X0 X1
       grind)
    | exact resolve eq30441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30441
  have eq32318 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6992 X1 X0 (σ X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6992
  have eq32319 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32318 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32318
  have eq32320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32319 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32319
    | (have j0 := eq32319 X0 X1
       grind)
    | exact resolve eq32319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32319
  have eq34764 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq837 X3 X2 (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) X4 X5
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq837
    | exact resolve eq837 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34767 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X4 (M.op (M.op X5 X4) X0))) (M.op (M.op X1 (M.op X2 X3)) (M.op X4 (M.op (M.op X5 X4) X0)))) = (M.op X6 (M.op (M.op X7 X6) (M.op X3 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq837 X3 X2 (M.op (M.op X1 (M.op X2 X3)) (M.op X4 (M.op (M.op X5 X4) X0))) X6 X7
       have i₂ := eq837 X4 X5 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq837 eq837
    | exact resolve eq837 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34836 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq837 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq205 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq837 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq205 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq205 eq837
    | exact resolve eq837 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq35348 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq34836 X0 X1 x x x X5 X6
       have i₂ := eq8260 x X5 X6 x x
       grind)
    | exact superpose eq8260 eq34836
    | exact resolve eq34836 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34836
  have eq35401 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X6 (M.op (M.op X7 X6) (M.op X3 (M.op X0 X0)))) = (M.op (M.op X4 (M.op (M.op X5 X4) X0)) (M.op (M.op X1 (M.op X2 X3)) (M.op X4 (M.op (M.op X5 X4) X0)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq34767 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq2253 (M.op X4 (M.op (M.op X5 X4) X0)) (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq2253 eq34767
    | exact resolve eq34767 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34767
  have eq35404 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq34764 X0 X1 X2 X3 X4 X5
       have i₂ := eq2253 (M.op X0 X0) (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq2253 eq34764
    | exact resolve eq34764 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34764
  have eq35559 : ∀ X0 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op (M.op X5 X4) X0)) (M.op X4 (M.op (M.op X5 X4) X0)))) = (M.op X6 (M.op (M.op X7 X6) (M.op X3 (M.op X0 X0)))) := by
    intro X0 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq35401 X0 x X2 X3 X4 X5 X6 X7
       have i₂ := eq4025 x (M.op X2 X3) (M.op X4 (M.op (M.op X5 X4) X0))
       grind)
    | exact superpose eq4025 eq35401
    | exact resolve eq35401 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35401
  have eq35562 : ∀ X0 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) = (M.op (M.op X2 X3) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq35404 X0 x X2 X3 X4 X5
       have i₂ := eq4025 x (M.op X2 X3) (M.op X0 X0)
       grind)
    | exact superpose eq4025 eq35404
    | exact resolve eq35404 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35404
  have eq35627 : ∀ X0 X2 X3 X4 X5 X6 X7 : G, (M.op X6 (M.op (M.op X7 X6) (M.op X3 (M.op X0 X0)))) = (M.op (M.op X2 X3) (M.op (M.op (M.op X5 X4) X0) (M.op X4 (M.op (M.op X5 X4) X0)))) := by
    intro X0 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq35559 X0 X2 X3 X4 X5 X6 X7
       have i₂ := eq2253 (M.op (M.op X5 X4) X0) X4 X4
       grind)
    | exact superpose eq2253 eq35559
    | exact resolve eq35559 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35559
  have eq35630 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq35562 X0 X2 X3 X4 X5
       have i₂ := eq2253 X0 X0 X0
       grind)
    | exact superpose eq2253 eq35562
    | exact resolve eq35562 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35562
  have eq35661 : ∀ X0 X2 X3 X6 X7 : G, (M.op (M.op X2 X3) X0) = (M.op X6 (M.op (M.op X7 X6) (M.op X3 (M.op X0 X0)))) := by
    intro X0 X2 X3 X6 X7
    first
    | (have i₁ := eq35627 X0 X2 X3 x x X6 X7
       have i₂ := eq220 x x X0 (M.op x x)
       grind)
    | exact superpose eq220 eq35627
    | exact resolve eq35627 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35627
  have eq35763 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq35348 X3 X4 X2 (M.op (M.op X1 X2) (M.op X0 X0))
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq35348
    | exact resolve eq35348 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35891 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 X3 X4 X5
       have i₂ := eq35348 X1 X2 X0 X3
       grind)
    | exact superpose eq35348 eq9
    | exact resolve eq9 eq35348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35895 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 X3
       have i₂ := eq35348 X1 X2 X0 X3
       grind)
    | exact superpose eq35348 eq75
    | exact resolve eq75 eq35348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq35935 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1129 x x
       have i₂ := eq35348 X0 X1 x x
       grind)
    | exact superpose eq35348 eq1129
    | exact resolve eq1129 eq35348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36326 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35935 X0 X1 X2 X3
       have i₂ := eq8260 (M.op X2 X1) (M.op X0 X3) X3 X0 X1
       grind)
    | exact superpose eq8260 eq35935
    | exact resolve eq35935 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35935
  have eq36430 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq35763 X0 X1 X2 X3 X4
       have i₂ := eq2253 (M.op X0 X0) (M.op X1 X2) (M.op X1 X2)
       grind)
    | exact superpose eq2253 eq35763
    | exact resolve eq35763 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35763
  have eq36547 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq36430 X0 x X2 X3 X4
       have i₂ := eq4025 x X2 (M.op X0 X0)
       grind)
    | exact superpose eq4025 eq36430
    | exact resolve eq36430 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36430
  have eq36597 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq36547 X0 X2 X3 X4
       have i₂ := eq2253 X0 X0 X0
       grind)
    | exact superpose eq2253 eq36547
    | exact resolve eq36547 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36547
  have eq39324 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1453 X2 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) X3
       have i₂ := eq134 X0 (M.op X2 (M.op X2 X2)) X1
       grind)
    | exact superpose eq134 eq1453
    | exact resolve eq1453 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39504 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq134 (M.op (M.op X1 (M.op X1 X1)) X0) X1 x
       have i₂ := eq1453 X1 X0 x
       grind)
    | exact superpose eq1453 eq134
    | exact resolve eq134 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39778 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39504 X0 X1
       have i₂ := eq4025 (M.op X1 (M.op X1 X1)) X0 (M.op (M.op X1 (M.op X1 X1)) X0)
       grind)
    | exact superpose eq4025 eq39504
    | exact resolve eq39504 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39504
  have eq39877 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39324 X0 X1 X2 X3
       have i₂ := eq4025 (M.op X1 (M.op X2 (M.op X2 X2))) X0 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0)
       grind)
    | exact superpose eq4025 eq39324
    | exact resolve eq39324 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39324
  have eq40051 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39778 X0 X1
       have i₂ := eq2253 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2253 eq39778
    | exact resolve eq39778 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39778
  have eq40091 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39877 X0 X1 X2 X3
       have i₂ := eq2253 X0 (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X1 (M.op X2 (M.op X2 X2)))
       grind)
    | exact superpose eq2253 eq39877
    | exact resolve eq39877 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39877
  have eq40177 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40051 X0 X1
       have i₂ := eq4025 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq4025 eq40051
    | exact resolve eq40051 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40051
  have eq40198 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X2 (M.op X2 X2)) (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq40091 X0 x X2 X3
       have i₂ := eq4025 x (M.op X2 (M.op X2 X2)) X0
       grind)
    | exact superpose eq4025 eq40091
    | exact resolve eq40091 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40091
  have eq40258 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq40198 X0 X2 X3
       have i₂ := eq3292 X0 X2 X2 X2
       grind)
    | exact superpose eq3292 eq40198
    | exact resolve eq40198 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292 eq40198
  have eq58286 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1453 X1 (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X2
       have i₂ := eq40177 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq40177 eq1453
    | exact resolve eq1453 eq40177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq40177
  have eq58329 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58286 X0 X1 X2
       have i₂ := eq4025 (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))
       grind)
    | exact superpose eq4025 eq58286
    | exact resolve eq58286 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58286
  have eq58554 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58329 X0 X1 X2
       have i₂ := eq1592 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X0 X0)
       grind)
    | exact superpose eq1592 eq58329
    | exact resolve eq58329 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58329
  have eq58670 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58554 X0 X1 X2
       have i₂ := eq8260 X1 X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))) (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact superpose eq8260 eq58554
    | exact resolve eq58554 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58554
  have eq58726 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op X1 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58670 X0 X1 X2
       have i₂ := eq4025 X0 X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))
       grind)
    | exact superpose eq4025 eq58670
    | exact resolve eq58670 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58670
  have eq58756 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58726 X0 X1 X2
       have i₂ := eq2253 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2253 eq58726
    | exact resolve eq58726 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58726
  have eq58778 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58756 X0 X0 X2
       have i₂ := eq4025 X0 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq4025 eq58756
    | exact resolve eq58756 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58756
  have eq58790 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58778 X0 X1 X2
       have i₂ := eq77 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq77 eq58778
    | exact resolve eq58778 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58778
  have eq61428 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ X2) (σ X2))) X2) = (τ (M.op X0 (M.op (M.op X1 X0) (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X2
       have i₂ := eq134 (σ X2) X0 X1
       grind)
    | exact superpose eq134 eq85
    | exact resolve eq85 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq134
  have eq79771 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X0) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))))) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3206 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))))) X4 X0
       have i₂ := eq35895 X1 X2 X3 X0
       grind)
    | exact superpose eq35895 eq3206
    | exact resolve eq3206 eq35895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79949 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X0) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) = (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq79771 X0 X1 X2 X3 X4
       have i₂ := eq2253 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))) X0 X0
       grind)
    | exact superpose eq2253 eq79771
    | exact resolve eq79771 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79771
  have eq80252 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X0) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) = (M.op (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq79949 X0 X1 X2 X3 X4
       have i₂ := eq890 X0 X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))
       grind)
    | exact superpose eq890 eq79949
    | exact resolve eq79949 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq79949
  have eq80409 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) = (M.op (M.op X4 X0) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq80252 X0 X1 X2 X3 X4
       have i₂ := eq8260 X1 X0 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))))) X2 (M.op X3 X2)
       grind)
    | exact superpose eq8260 eq80252
    | exact resolve eq80252 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80252
  have eq80501 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X0) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq80409 X0 X1 X2 X3 X4
       have i₂ := eq35895 X1 X2 X3 X0
       grind)
    | exact superpose eq35895 eq80409
    | exact resolve eq80409 eq35895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35895 eq80409
  have eq82204 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36326 X2 X3 X4 X1
       have i₂ := eq3889 X2 X1 X1 X0
       grind)
    | (have i₁ := eq36326 X2 X3 X4 X1
       have i₂ := eq3889 X0 X1 X1 X2
       grind)
    | exact superpose eq3889 eq36326
    | exact resolve eq36326 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889 eq36326
  have eq109342 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq58790 X5 (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) X1
       have i₂ := eq837 X3 X4 X0 X1 X2
       grind)
    | exact superpose eq837 eq58790
    | exact resolve eq58790 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq58790
  have eq110058 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq109342 X0 X1 X2 X3 X4 X5
       have i₂ := eq2253 (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X2 X1) (M.op X2 X1)
       grind)
    | exact superpose eq2253 eq109342
    | exact resolve eq109342 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109342
  have eq110225 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110058 X0 X1 X0 X3 X4 X5
       have i₂ := eq4025 X0 X1 (M.op X3 (M.op (M.op X4 X3) X0))
       grind)
    | exact superpose eq4025 eq110058
    | exact resolve eq110058 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110058
  have eq110311 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110225 X0 X1 X2 X1 X4 X5
       have i₂ := eq2253 (M.op (M.op X4 X1) X0) X1 X1
       grind)
    | exact superpose eq2253 eq110225
    | exact resolve eq110225 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253 eq110225
  have eq110346 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X5 (M.op X1 X0))) = (M.op (M.op (M.op X2 X1) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110311 X2 X1 X2 X0 X1 X5
       have i₂ := eq220 X0 X1 X2 (M.op X1 X0)
       grind)
    | exact superpose eq220 eq110311
    | exact resolve eq110311 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq110311
  have eq110363 : ∀ X0 X1 X5 : G, (M.op X0 (M.op X5 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X5 (M.op X1 X0))) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq110346 X0 X1 x x x X5
       have i₂ := eq8260 (M.op x x) X0 (M.op X5 (M.op X1 X0)) (M.op x X1) x
       grind)
    | exact superpose eq8260 eq110346
    | exact resolve eq110346 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110346
  have eq120788 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X3))) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X4 (M.op X5 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110363 X3 X5 X4
       have i₂ := eq35348 X1 X2 X0 X3
       grind)
    | exact superpose eq35348 eq110363
    | exact resolve eq110363 eq35348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35348 eq110363
  have eq121556 : ∀ X0 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X3))) = (M.op (M.op X0 X3) (M.op X4 (M.op X5 X3))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq120788 X0 x x X3 X4 X5
       have i₂ := eq8260 (M.op x x) (M.op X0 X3) (M.op X4 (M.op X5 X3)) X0 x
       grind)
    | exact superpose eq8260 eq120788
    | exact resolve eq120788 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120788
  have eq127759 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (σ X2)) (σ X2)) = (M.op (σ X2) (M.op X3 (M.op (M.op X4 X3) (M.op (σ X0) (σ X0))))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq82204 X1 (σ X2) (σ X2) X3 X4
       have i₂ := eq177 X2 X0
       grind)
    | (have i₁ := eq82204 X0 (σ X1) (σ X1) X3 X4
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq82204
    | (have j1 := eq177 X2 X0
       grind)
    | exact resolve eq82204 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq82204
  have eq128794 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (M.op (M.op X1 (σ X2)) (σ X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127759 X0 X1 X2 x x
       have i₂ := eq9 (σ X0) x x
       grind)
    | exact superpose eq9 eq127759
    | (have j0 := eq127759 X0 X1 X2 x x
       grind)
    | exact resolve eq127759 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127759
  have eq129167 : ∀ X0 X2 : G, (M.op (σ X2) (σ X2)) = (M.op (σ X2) (σ X0)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq128794 X0 x X2
       have i₂ := eq1129 (σ X2) x
       grind)
    | exact superpose eq1129 eq128794
    | (have j0 := eq128794 X0 x X2
       grind)
    | exact resolve eq128794 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128794
  have eq157813 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op (M.op X1 X0) (σ (τ X2))))) = (τ (k (M.op (σ (τ X2)) (σ (τ X2))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X2 (M.op (σ (τ X2)) (σ (τ X2)))
       have i₂ := eq61428 X0 X1 (τ X2)
       grind)
    | exact superpose eq61428 eq32
    | exact resolve eq32 eq61428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61428
  have eq157900 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op (M.op X1 X0) X2))) = (τ (k (M.op X2 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157813 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq157813
    | exact resolve eq157813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157813
  have eq157987 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op (M.op X1 X0) X2))) = (τ (M.op X2 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157900 X0 X1 X2
       have i₂ := eq71 X2
       grind)
    | exact superpose eq71 eq157900
    | exact resolve eq157900 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157900
  have eq158155 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157987 x x (M.op X1 (M.op X2 X2))
       have i₂ := eq35661 X2 X0 X1 x x
       grind)
    | exact superpose eq35661 eq157987
    | exact resolve eq157987 eq35661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35661 eq157987
  have eq158380 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (M.op (M.op X2 X2) (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158155 X0 X1 X2
       have i₂ := eq4025 X1 (M.op X2 X2) (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq4025 eq158155
    | exact resolve eq158155 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158155
  have eq158475 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (M.op (M.op X2 X2) (M.op (M.op X2 X2) (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158380 X0 X1 X2
       have i₂ := eq1592 (M.op X2 X2) X1 (M.op X2 X2) X1
       grind)
    | exact superpose eq1592 eq158380
    | exact resolve eq158380 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592 eq158380
  have eq158501 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (M.op X2 (M.op (M.op X2 X2) (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158475 X0 X1 X2
       have i₂ := eq10136 X1 (M.op X2 X2) X2 X2
       grind)
    | exact superpose eq10136 eq158475
    | exact resolve eq158475 eq10136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158475
  have eq158511 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (M.op X2 (M.op X2 (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158501 X0 X1 X2
       have i₂ := eq121556 X2 X2 X1 X2
       grind)
    | exact superpose eq121556 eq158501
    | exact resolve eq158501 eq121556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158501
  have eq215552 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X3 (M.op X3 X3)) (M.op (M.op X3 (M.op X3 X3)) (M.op X3 (M.op X3 X3))))) = (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36597 (M.op X3 (M.op X3 X3)) X4 X2 x
       have i₂ := eq35630 X3 x X2 X0 X1
       grind)
    | exact superpose eq35630 eq36597
    | exact resolve eq36597 eq35630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35630 eq36597
  have eq217194 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X3 X3) (M.op (M.op X3 (M.op X3 X3)) (M.op X3 (M.op X3 X3))))) = (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq215552 X0 X1 X2 X3 X4
       have i₂ := eq4025 X3 (M.op X3 X3) (M.op X3 (M.op X3 X3))
       grind)
    | exact superpose eq4025 eq215552
    | exact resolve eq215552 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215552
  have eq218074 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X3 X3)) = (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq217194 X0 X1 X2 X3 X4
       have i₂ := eq77 X3 X3 (M.op X3 X3) X3
       grind)
    | exact superpose eq77 eq217194
    | exact resolve eq217194 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq217194
  have eq286954 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32320 (τ X1) (τ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq32320
    | (have j0 := eq32320 (τ X0) (τ X1)
       grind)
    | exact resolve eq32320 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32320
  have eq287154 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq286954 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286954
    | (have j0 := eq286954 X0 X1
       grind)
    | exact resolve eq286954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286954
  have eq287198 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq287154 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq287154
    | (have j0 := eq287154 X0 X1
       grind)
    | exact resolve eq287154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287154
  have eq287225 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq287198 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq287198
    | (have j0 := eq287198 X0 X1
       grind)
    | exact resolve eq287198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287198
  have eq287242 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq287225 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287225
    | (have j0 := eq287225 X0 X1
       grind)
    | exact resolve eq287225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287225
  have eq287252 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq287242 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287242
    | (have j0 := eq287242 X0 X1
       grind)
    | exact resolve eq287242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287242
  have eq287259 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq287252 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq287252
    | (have j0 := eq287252 X0 X1
       grind)
    | exact resolve eq287252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287252
  have eq287266 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq287259 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287259
    | (have j0 := eq287259 X0 X1
       grind)
    | exact resolve eq287259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287259
  have eq287273 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq287266 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq287266
    | (have j0 := eq287266 X0 X1
       grind)
    | exact resolve eq287266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287266
  have eq287481 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq287273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287273
  have eq313783 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq287481 (σ X0) (σ X1)
       have i₂ := eq30590 X0 X1
       grind)
    | (have i₁ := eq287481 (σ X0) (σ X0)
       have i₂ := eq30590 X0 X1
       grind)
    | exact superpose eq30590 eq287481
    | (have j0 := eq287481 (σ X0) (σ X1)
       have j1 := eq30590 X0 X1
       grind)
    | (have r₁ := eq287481 (σ X1) (σ X1)
       have r₂ := eq30590 X1 X1
       grind)
    | (have r₁ := eq287481 (σ X0) (σ X0)
       have r₂ := eq30590 X0 X0
       grind)
    | exact resolve eq287481 eq30590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30590 eq287481
  have eq313785 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq313783 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313783
  have eq313789 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq313785 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq313785
    | (have j0 := eq313785 X0 X1
       grind)
    | exact resolve eq313785 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313785
  have eq313790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq313789 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313789
  have eq313891 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq313790 X1 X0
       have j1 := eq129167 X0 X1
       grind)
    | (have r₁ := eq313790 x X0
       have r₂ := eq129167 X0 x
       grind)
    | (have r₁ := eq313790 X0 X0
       have r₂ := eq129167 X0 X0
       grind)
    | exact resolve eq313790 eq129167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129167 eq313790
  have eq313957 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq313891 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq313891
    | (have j0 := eq313891 (τ X1) (τ X0)
       grind)
    | exact resolve eq313891 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq313891
  have eq314111 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq313957 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq313957
    | (have j0 := eq313957 X0 X1
       grind)
    | exact resolve eq313957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313957
  have eq314145 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq314111 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq314111
    | (have j0 := eq314111 X0 X1
       grind)
    | exact resolve eq314111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314111
  have eq314158 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq314145 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq314145
    | (have j0 := eq314145 X0 X1
       grind)
    | exact resolve eq314145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314145
  have eq314168 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq314158 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq314158
    | (have j0 := eq314158 X0 X1
       grind)
    | exact resolve eq314158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314158
  have eq314177 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq314168 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq314168
    | (have j0 := eq314168 X0 X1
       grind)
    | exact resolve eq314168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314168
  have eq314277 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq314177 X0 (τ X1)
       grind)
    | exact superpose eq314177 eq19
    | (have j1 := eq314177 X0 (τ X1)
       grind)
    | exact resolve eq19 eq314177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq315408 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (σ (M.op X2 (k (τ X0) X1))) ∨ (M.op (k (τ X0) X1) (k (τ X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq314277 X0 (k X0 (σ X1))
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq314277
    | exact resolve eq314277 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq314277
  have eq710438 : ∀ X0 X1 X2 : G, (k (σ X0) (k X1 (σ X2))) = (σ (M.op X0 (k (τ X1) X2))) ∨ (M.op (k (τ X1) X2) (k (τ X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq315408 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315408
  have eq710619 : ∀ X0 X1 : G, (σ (k X0 (M.op (τ (σ X1)) (M.op (τ (σ X1)) (τ (σ X1)))))) = (σ (M.op X0 (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1))) ∨ (M.op (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq967 (σ X1) X0
       have i₂ := eq710438 X0 (σ (M.op (τ (σ X1)) (τ (σ X1)))) X1
       grind)
    | exact superpose eq710438 eq967
    | (have j1 := eq710438 X0 (σ (M.op (τ (σ X1)) (τ (σ X1)))) X1
       grind)
    | exact resolve eq967 eq710438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq710438
  have eq710698 : ∀ X0 X1 : G, (σ (k X0 (M.op (τ (σ X1)) (M.op (τ (σ X1)) (τ (σ X1)))))) = (σ (M.op X0 (k (M.op (τ (σ X1)) (τ (σ X1))) X1))) ∨ (M.op (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq710619 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (τ (σ X1)))
       grind)
    | exact superpose eq10 eq710619
    | (have j0 := eq710619 X0 X1
       grind)
    | exact resolve eq710619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710619
  have eq710777 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (k (M.op X1 X1) X1))) ∨ (M.op (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq710698 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq710698
    | (have j0 := eq710698 X0 X1
       grind)
    | exact resolve eq710698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710698
  have eq710840 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (M.op X1 (M.op X1 X1)))) ∨ (M.op (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq710777 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq710777
    | (have j0 := eq710777 X0 X1
       grind)
    | exact resolve eq710777 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710777
  have eq710882 : ∀ X0 X1 : G, (M.op (k (M.op (τ (σ X1)) (τ (σ X1))) X1) (k (M.op (τ (σ X1)) (τ (σ X1))) X1)) = X0 ∨ (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq710840 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (τ (σ X1)))
       grind)
    | exact superpose eq10 eq710840
    | (have j0 := eq710840 X0 X1
       grind)
    | exact resolve eq710840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710840
  have eq710911 : ∀ X0 X1 : G, (M.op (k (M.op X1 X1) X1) (k (M.op X1 X1) X1)) = X0 ∨ (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq710882 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq710882
    | (have j0 := eq710882 X0 X1
       grind)
    | exact resolve eq710882 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710882
  have eq710932 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) = X0 ∨ (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq710911 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq710911
    | (have j0 := eq710911 X0 X1
       grind)
    | exact resolve eq710911 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq710911
  have eq710945 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 ∨ (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq710932 X0 X1
       have i₂ := eq40258 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq40258 eq710932
    | (have j0 := eq710932 X0 X1
       grind)
    | exact resolve eq710932 eq40258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710932
  have eq710954 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 (M.op X1 X1)))) = (σ (M.op X0 (M.op X1 (M.op X1 X1)))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq710945 X0 X1
       have i₂ := eq223 X1 X1 X1
       grind)
    | exact superpose eq223 eq710945
    | (have j0 := eq710945 X0 X1
       grind)
    | exact resolve eq710945 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq710945
  have eq937857 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X1))) = (τ (σ (M.op X0 (M.op X1 (M.op X1 X1))))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X1 (M.op X1 X1)))
       have i₂ := eq710954 X0 X1
       grind)
    | exact superpose eq710954 eq10
    | (have j1 := eq710954 (k X0 (M.op X1 (M.op X1 X1))) (τ (σ (M.op X0 (M.op X1 (M.op X1 X1)))))
       grind)
    | exact resolve eq10 eq710954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710954
  have eq938046 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = (k X0 (M.op X1 (M.op X1 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq937857 X0 X1
       have i₂ := eq10 (M.op X0 (M.op X1 (M.op X1 X1)))
       grind)
    | exact superpose eq10 eq937857
    | (have j0 := eq937857 (M.op X0 (M.op X1 (M.op X1 X1))) (k X0 (M.op X1 (M.op X1 X1)))
       grind)
    | exact resolve eq937857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937857
  have eq938352 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) = (k X4 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938046 X0 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))
       have i₂ := eq218074 X0 X1 X2 X3 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))
       grind)
    | exact superpose eq218074 eq938046
    | (have j0 := eq938046 (M.op X4 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) (k X4 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3))))
       grind)
    | exact resolve eq938046 eq218074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218074 eq938046
  have eq938683 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X3) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) = (M.op X4 (M.op (M.op X0 X3) (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938352 X3 X4 X2 X3 X4
       have i₂ := eq8260 (M.op X2 X4) (M.op X3 X3) (M.op (M.op X3 (M.op X4 (M.op (M.op X2 X4) (M.op X3 X3)))) (M.op X3 X3)) X3 X4
       grind)
    | exact superpose eq8260 eq938352
    | (have j0 := eq938352 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq938352 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8260 eq938352
  have eq938787 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) = (M.op X4 (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) (M.op X3 X3)))) ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938683 X0 X1 X2 x X4
       have i₂ := eq121556 X0 x (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 x)))) x
       grind)
    | exact superpose eq121556 eq938683
    | (have j0 := eq938683 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq938683 eq121556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121556 eq938683
  have eq938855 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3))) (M.op X3 (M.op X3 X3)))) = (M.op X4 (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3))) (M.op X3 (M.op X3 X3)))) ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938787 X4 X1 X2 X0 X4
       have i₂ := eq10136 X0 X0 (M.op X1 (M.op (M.op X2 X1) (M.op X4 X0))) X4
       grind)
    | exact superpose eq10136 eq938787
    | (have j0 := eq938787 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq938787 eq10136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10136 eq938787
  have eq938905 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op X3 (M.op X3 (M.op (M.op (M.op X2 X1) (M.op X0 X3)) X3)))) = (M.op X4 (M.op X3 (M.op X3 (M.op (M.op (M.op X2 X1) (M.op X0 X3)) X3)))) ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938855 X0 X3 X2 X0 X4
       have i₂ := eq40258 X0 (M.op (M.op X2 X3) (M.op X0 X0)) X3
       grind)
    | exact superpose eq40258 eq938855
    | (have j0 := eq938855 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq938855 eq40258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40258 eq938855
  have eq938921 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op X3 (M.op (M.op X0 X3) (M.op X3 X3)))) = (M.op X4 (M.op X3 (M.op (M.op X0 X3) (M.op X3 X3)))) ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938905 X0 X1 X2 X2 X4
       have i₂ := eq4025 (M.op X2 X1) (M.op X0 X2) X2
       grind)
    | exact superpose eq4025 eq938905
    | (have j0 := eq938905 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq938905 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4025 eq938905
  have eq938933 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 X3)))) = X4 ∨ (M.op X4 X3) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq938921 X2 X1 X2 X0 X4
       have i₂ := eq9 X0 X0 X2
       grind)
    | exact superpose eq9 eq938921
    | (have j0 := eq938921 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq938921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938921
  have eq1011231 : ∀ X0 X1 X2 X3 : G, (τ X0) = (τ (M.op (M.op X1 (M.op X2 X3)) X3)) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq158511 X1 (M.op X2 X3) X3
       have i₂ := eq938933 X3 X3 X2 X3 X0
       grind)
    | (have i₁ := eq158511 X0 X1 X2
       have i₂ := eq938933 X0 X1 X2 X3 (M.op X2 (M.op X2 (M.op X1 (M.op X2 X2))))
       grind)
    | exact superpose eq938933 eq158511
    | (have j1 := eq938933 X0 X1 X2 X3 X0
       grind)
    | exact resolve eq158511 eq938933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158511
  have eq1011248 : ∀ X0 X1 X2 X6 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X6 ∨ (M.op X0 X6) = (k X0 X6) := by
    intro X0 X1 X2 X6
    first
    | (have i₁ := eq35891 x x x X6 X1 X2
       have i₂ := eq938933 x x x X6 X0
       grind)
    | (have i₁ := eq35891 X0 X1 X2 x x x
       have i₂ := eq938933 X0 X1 X2 x (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 x))))
       grind)
    | exact superpose eq938933 eq35891
    | (have j1 := eq938933 X0 X1 X2 X6 X0
       grind)
    | exact resolve eq35891 eq938933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35891 eq938933
  have eq1012650 : ∀ X0 X3 : G, (τ X0) = (τ (M.op X3 X3)) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq1011231 X0 x x X3
       have i₂ := eq3206 X3 x x
       grind)
    | exact superpose eq3206 eq1011231
    | (have j0 := eq1011231 X0 x x X3
       grind)
    | exact resolve eq1011231 eq3206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3206 eq1011231
  have eq1018632 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) X0) = X2 ∨ (M.op (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X3 X2) X2))) X0) = (k (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X3 X2) X2))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq80501 X2 (M.op X3 X2) X4 X5 X1
       have i₂ := eq1011248 (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X3 X2) X2))) X2 X3 X0
       grind)
    | (have i₁ := eq80501 X0 X1 X2 X3 X4
       have i₂ := eq1011248 X0 X1 X2 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0)))))
       grind)
    | exact superpose eq1011248 eq80501
    | (have j1 := eq1011248 (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X3 X2) X2))) X1 X2 X0
       grind)
    | exact resolve eq80501 eq1011248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80501 eq1011248
  have eq1019580 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 (M.op (M.op X5 X4) (M.op X2 X2))) X0) = (k (M.op X4 (M.op (M.op X5 X4) (M.op X2 X2))) X0) ∨ (M.op (M.op X1 X2) X0) = X2 := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq1018632 X0 X1 X0 X1 X4 X5
       have i₂ := eq1129 X0 X1
       grind)
    | exact superpose eq1129 eq1018632
    | (have j0 := eq1018632 X0 X1 X2 x X4 X5
       grind)
    | exact resolve eq1018632 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018632
  have eq1020122 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1019580 X0 X1 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1019580
    | (have j0 := eq1019580 X0 X1 X2 x x
       grind)
    | exact resolve eq1019580 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019580
  have eq1029851 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) = X3 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3897 X3 X1 (M.op X2 X0)
       have i₂ := eq1020122 X3 X2 X0
       grind)
    | exact superpose eq1020122 eq3897
    | (have j1 := eq1020122 X3 X1 X0
       grind)
    | exact resolve eq3897 eq1020122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897 eq1020122
  have eq1031046 : ∀ X0 X3 : G, (M.op X0 (M.op X3 X0)) = X3 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq1029851 X0 x x X3
       have i₂ := eq3278 X3 X0 x x
       grind)
    | exact superpose eq3278 eq1029851
    | (have j0 := eq1029851 X0 x x X3
       grind)
    | exact resolve eq1029851 eq3278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3278 eq1029851
  have eq1035370 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq142 X0
       have i₂ := eq1031046 X0 X0
       grind)
    | exact superpose eq1031046 eq142
    | (have j1 := eq1031046 X0 X0
       grind)
    | exact resolve eq142 eq1031046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1031046
  have eq1036276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1035370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035370
  have eq1037696 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1036276 (σ X0)
       grind)
    | exact superpose eq1036276 eq15
    | exact resolve eq15 eq1036276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037835 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1037696 X0
       have i₂ := eq1036276 X0
       grind)
    | exact superpose eq1036276 eq1037696
    | exact resolve eq1037696 eq1036276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036276 eq1037696
  have eq1039529 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1012650 X1 (σ X0)
       have i₂ := eq1037835 X0
       grind)
    | exact superpose eq1037835 eq1012650
    | (have j0 := eq1012650 X1 (σ X0)
       grind)
    | exact resolve eq1012650 eq1037835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012650
  have eq1039553 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1129 (σ X0) (σ X0)
       have i₂ := eq1037835 X0
       grind)
    | exact superpose eq1037835 eq1129
    | exact resolve eq1129 eq1037835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037835
  have eq1039966 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1039529 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1039529
    | (have j0 := eq1039529 X0 X1
       grind)
    | exact resolve eq1039529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039529
  have eq1092274 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1039966 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039966
  have eq1251121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1092274 X1 (σ X0)
       grind)
    | exact superpose eq1092274 eq15
    | (have j1 := eq1092274 X1 (σ X0)
       grind)
    | exact resolve eq15 eq1092274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092274
  have eq1251231 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1251121 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1251121
    | (have j0 := eq1251121 X0 X1
       grind)
    | exact resolve eq1251121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251121
  have eq1251411 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq314177 eq1251231
    | (have j0 := eq1251231 X0 X1
       have j1 := eq314177 X0 X1
       grind)
    | exact resolve eq1251231 eq314177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314177 eq1251231
  have eq1258659 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1251411 x y
       grind)
    | exact superpose eq1251411 eq16
    | (have j1 := eq1251411 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1251411 x y
       grind)
    | exact resolve eq16 eq1251411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251411
  have eq1259359 : x = (M.op y y) := by grind
  clear eq1258659
  have eq1260036 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1039553 y
       have i₂ := eq1259359
       grind)
    | exact superpose eq1259359 eq1039553
    | exact resolve eq1039553 eq1259359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039553
  have eq1260137 : x = (M.op x y) := by
    first
    | (have i₁ := eq1129 y y
       have i₂ := eq1259359
       grind)
    | exact superpose eq1259359 eq1129
    | exact resolve eq1129 eq1259359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq1259359
  have eq1260610 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1260137
       grind)
    | exact superpose eq1260137 eq16
    | exact resolve eq16 eq1260137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260137
  have eq1261125 : False := by grind
  exact eq1261125

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
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
  clear eq37
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq102
    | (have j0 := eq102 (σ X0)
       grind)
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq44
    | (have j1 := eq102 x
       grind)
    | exact resolve eq44 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq379 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1313 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq192 eq445
    | exact resolve eq445 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1331 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq445 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq445 X0 X0 X0
       grind)
    | exact superpose eq445 eq445
    | exact resolve eq445 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq1364 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq445 X0 X0 X0
       grind)
    | exact superpose eq445 eq51
    | exact resolve eq51 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1372 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq379 (M.op x (M.op x x))
       have i₂ := eq445 x x x
       grind)
    | exact superpose eq445 eq379
    | exact resolve eq379 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq445
  have eq1387 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1363 X0
       have i₂ := eq476 X0 X0
       grind)
    | exact superpose eq476 eq1363
    | exact resolve eq1363 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1363
  have eq1408 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq191 eq1313
    | exact resolve eq1313 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq2038 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1372 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1372
    | exact resolve eq1372 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq2079 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2038 X0 X1
       have i₂ := eq1364 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1364 eq2038
    | exact resolve eq2038 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2093 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2079 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2079
    | exact resolve eq2079 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq4427 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq37389 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2093 eq14
    | exact resolve eq14 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093
  have eq37886 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq37389 eq1331
    | exact resolve eq1331 eq37389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331 eq37389
  have eq37911 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq191 eq37886
    | exact resolve eq37886 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq37886
  have eq37960 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37911 X0 X1
       have i₂ := eq1364 (M.op X0 (M.op y X0))
       grind)
    | exact superpose eq1364 eq37911
    | exact resolve eq37911 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq37911
  have eq37986 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq391 eq37960
    | exact resolve eq37960 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq37960
  have eq39769 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq37986 eq1408
    | exact resolve eq1408 eq37986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq37986
  have eq45177 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39769 X0 y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq39769
    | exact resolve eq39769 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq45238 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f45238_13 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
      intro X0
      grind
    have f45238_14 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
      intro X0 X1
      grind
    have f45238_22 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) := by grind
    have f45238_23 : y ≠ x := by grind
    have f45238_24 : y ≠ (M.op x x) := by grind
    have f45238_26 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ y = (M.op x x) := by
      intro X0
      first
      | (have j0 := f45238_13 X0
         grind)
      | (have r₁ := f45238_13 X0
         have r₂ := f45238_22
         grind)
      | exact resolve f45238_13 f45238_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f45238_27 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) := by
      intro X0
      first
      | (have j0 := f45238_26 X0
         grind)
      | (have r₁ := f45238_26 X0
         have r₂ := f45238_24
         grind)
      | exact resolve f45238_26 f45238_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f45238_28 : y = x := by
      first
      | (have i₁ := f45238_27 x
         have i₂ := f45238_14 x x
         grind)
      | exact superpose f45238_14 f45238_27
      | exact resolve f45238_27 f45238_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f45238_29 : False := by
      first
      | (have r₁ := f45238_28
         have r₂ := f45238_23
         grind)
      | exact resolve f45238_28 f45238_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f45238_29
  clear eq45177
  have eq72700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq45238 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq45238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq72700
    | exact resolve eq72700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72700
  have eq72712 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq72701
       have r₂ := eq28
       grind)
    | exact resolve eq72701 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72701
  have eq72805 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq72712 eq39769
    | exact resolve eq39769 eq72712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72712
  have eq72888 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq39769 eq72805
    | exact resolve eq72805 eq39769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39769 eq72805
  have eq72946 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq72888
  have eq73152 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq72946
    | exact resolve eq72946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72946
  have eq75453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq73152 eq45238
    | exact resolve eq45238 eq73152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45238 eq73152
  have eq75455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq75453
  have eq75457 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq75455
       have r₂ := eq28
       grind)
    | exact resolve eq75455 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75455
  have eq75460 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq345
       have i₂ := eq75457
       grind)
    | exact superpose eq75457 eq345
    | exact resolve eq345 eq75457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75464 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq75457
  have eq75601 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq75460
  have eq75692 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75464
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75464
    | exact resolve eq75464 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75464
  have eq75694 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75601
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq75601
    | exact resolve eq75601 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75601
  have eq78774 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq75692
       grind)
    | exact superpose eq75692 eq70
    | exact resolve eq70 eq75692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75692
  have eq78792 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq78774
    | exact resolve eq78774 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78774
  have eq78793 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75694
       have i₂ := eq102 sF2
       grind)
    | exact superpose eq102 eq75694
    | (have j1 := eq102 (σ x)
       grind)
    | exact resolve eq75694 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210685 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq78793
  have eq210954 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq210685
    | exact resolve eq210685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210685
  have eq215710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq210954 eq78792
    | exact resolve eq78792 eq210954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78792 eq210954
  have eq215714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq215710
  have eq215724 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq215714
       have r₂ := eq28
       grind)
    | exact resolve eq215714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215714
  have eq215734 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq216542 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq215734 eq75694
    | exact resolve eq75694 eq215734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75694 eq215734
  have eq216558 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq216542
  have eq216568 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq216558 eq215724
    | exact resolve eq215724 eq216558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215724 eq216558
  have eq216756 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq216568
  have eq216883 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq216756 eq30
    | exact resolve eq30 eq216756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq216756
  have eq217124 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq216883
    | exact resolve eq216883 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq216883
  have eq217125 : x = y := by grind
  clear eq217124
  have eq217291 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq217125
       grind)
    | exact superpose eq217125 eq19
    | exact resolve eq19 eq217125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq217292 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq217125
       grind)
    | exact superpose eq217125 eq25
    | exact resolve eq25 eq217125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq217125
  have eq217706 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq217292
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq217292
    | exact resolve eq217292 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217292
  have eq217731 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq217706 eq27
    | exact resolve eq27 eq217706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq217706
  have eq218036 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq345
       have i₂ := eq217291
       grind)
    | exact superpose eq217291 eq345
    | exact resolve eq345 eq217291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq218129 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1387 x
       have i₂ := eq217291
       grind)
    | exact superpose eq217291 eq1387
    | exact resolve eq1387 eq217291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq218375 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq218036
    | exact resolve eq218036 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218036
  have eq218509 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq235195 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218375 eq102
    | (have j0 := eq102 (σ x)
       grind)
    | exact resolve eq102 eq218375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq235196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217731 eq235195
    | exact resolve eq235195 eq217731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235195
  have eq235211 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq235196
       have r₂ := eq28
       grind)
    | exact resolve eq235196 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235196
  have eq235217 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217731 eq235211
    | exact resolve eq235211 eq217731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235211
  have eq235337 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq235217 eq218509
    | exact resolve eq218509 eq235217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218509 eq235217
  have eq235355 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217731 eq235337
    | exact resolve eq235337 eq217731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235337
  have eq235884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq235355 eq218375
    | exact resolve eq218375 eq235355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218375 eq235355
  have eq235890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq235884
  have eq235894 : x = (M.op x y) := by
    first
    | (have r₁ := eq235890
       have r₂ := eq28
       grind)
    | exact resolve eq235890 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235890
  have eq235906 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq235894 eq21
    | exact resolve eq21 eq235894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq236373 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq235894 eq218129
    | exact resolve eq218129 eq235894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218129
  have eq236387 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq236373
       have i₂ := eq217291
       grind)
    | exact superpose eq217291 eq236373
    | exact resolve eq236373 eq217291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217291 eq236373
  have eq236648 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq235906
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq235906
    | exact resolve eq235906 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235906
  have eq236651 : x = (k x x) := by
    first
    | exact superpose eq235894 eq236387
    | exact resolve eq236387 eq235894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235894 eq236387
  have eq237172 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4427 x
       have i₂ := eq236651
       grind)
    | exact superpose eq236651 eq4427
    | (have j0 := eq4427 x
       grind)
    | exact resolve eq4427 eq236651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427 eq236651
  have eq237176 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq237172
  have eq237185 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq237176
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq237176
    | exact resolve eq237176 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq237176
  have eq237203 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq217731 eq237185
    | exact resolve eq237185 eq217731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217731 eq237185
  have eq237219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq236648 eq237203
    | exact resolve eq237203 eq236648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236648 eq237203
  have eq237233 : False := by grind
  exact eq237233

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq19
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  clear eq24
  have eq58 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X1 X2) (k (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    grind
  have eq62 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq62
    | exact resolve eq62 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq104 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq63 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq140 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq67 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq67
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq173 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0
       have i₂ := eq159 X0 X1
       grind)
    | (have i₁ := eq67 X0
       have i₂ := eq159 X0 (M.op X0 X0)
       grind)
    | exact superpose eq159 eq67
    | (have j1 := eq159 X1 X0
       grind)
    | exact resolve eq67 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq101 X1 X1
       grind)
    | exact superpose eq101 eq104
    | exact resolve eq104 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq104
  have eq197 : ∀ X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X1 X3 X4
    first
    | (have i₁ := eq31 X3 x (M.op (M.op x x) (M.op X1 X1)) X4
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq256 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 X1 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq60
    | exact resolve eq60 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq268 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq173 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq288 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq256 X0 x (M.op X0 X0)
       have i₂ := eq197 x X0 X0
       grind)
    | exact superpose eq197 eq256
    | exact resolve eq256 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq269 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq269
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq269 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq269
    | exact resolve eq269 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq301 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq300
    | exact resolve eq300 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq299
    | exact resolve eq299 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq299
  have eq363 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq288 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq288
    | exact resolve eq288 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq1343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq302 X1
       grind)
    | exact superpose eq302 eq137
    | (have j0 := eq137 X0 X1
       grind)
    | exact resolve eq137 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1344 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1343 X0 X1
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq1343
    | (have j0 := eq1343 X0 X1
       grind)
    | exact resolve eq1343 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq1343
  have eq1408 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1344 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1344
    | (have j0 := eq1344 (τ X0) X1
       grind)
    | exact resolve eq1344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1532 : ∀ X0 X1 : G, (σ X1) = (σ (τ (M.op X0 X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1408 X0 X1
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq1408
    | (have j0 := eq1408 X0 X1
       grind)
    | exact resolve eq1408 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq1408
  have eq1542 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1532 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1532
    | (have j0 := eq1532 X0 X1
       grind)
    | exact resolve eq1532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1550 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1542 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq1542
    | (have j0 := eq1542 X0 X1
       grind)
    | exact resolve eq1542 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1542
  have eq2251 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 (M.op X0 X0) X2 X1
       have i₂ := eq190 X0 X0
       grind)
    | exact superpose eq190 eq70
    | exact resolve eq70 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq2396 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 (M.op X0 X1) X1 X3 X2
       have i₂ := eq2251 X1 X1 X0
       grind)
    | exact superpose eq2251 eq70
    | exact resolve eq70 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2251
  have eq2413 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2396 X0 X1 x x
       have i₂ := eq256 X1 x x
       grind)
    | exact superpose eq256 eq2396
    | exact resolve eq2396 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq2396
  have eq7932 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0
       have i₂ := eq1550 X0 X1
       grind)
    | exact superpose eq1550 eq67
    | (have j1 := eq1550 X0 X1
       grind)
    | exact resolve eq67 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1550
  have eq8085 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7932 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7932
  have eq8173 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq8085 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq8085 (σ X0) X1
       grind)
    | exact superpose eq8085 eq10
    | (have j1 := eq8085 X0 X1
       grind)
    | exact resolve eq10 eq8085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8085
  have eq8206 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8173 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8173
    | (have j0 := eq8173 (σ X0) X1
       grind)
    | exact resolve eq8173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq8401 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8206 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8206
    | (have j0 := eq8206 X0 X1
       grind)
    | exact resolve eq8206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8206
  have eq8905 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8401 x y
       grind)
    | exact superpose eq8401 eq16
    | (have j1 := eq8401 x y
       grind)
    | exact resolve eq16 eq8401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8401
  have eq9079 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8905
       have i₂ := eq159 y x
       grind)
    | exact superpose eq159 eq8905
    | (have j1 := eq159 y x
       grind)
    | exact resolve eq8905 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq8905
  have eq9097 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq9079
  have eq9098 : x = (M.op y y) := by grind
  clear eq9097
  have eq9123 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq363 y
       have i₂ := eq9098
       grind)
    | exact superpose eq9098 eq363
    | exact resolve eq363 eq9098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq9172 : x = (M.op x y) := by
    first
    | (have i₁ := eq2413 y y
       have i₂ := eq9098
       grind)
    | exact superpose eq9098 eq2413
    | exact resolve eq2413 eq9098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413 eq9098
  have eq9875 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9123
       grind)
    | exact superpose eq9123 eq16
    | exact resolve eq16 eq9123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9123
  have eq9921 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq9875
       have i₂ := eq9172
       grind)
    | exact superpose eq9172 eq9875
    | exact resolve eq9875 eq9172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9172 eq9875
  have eq9922 : False := by grind
  exact eq9922

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxx_y_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq52 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq66 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq67 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) (M.op X1 X1))) = X1 := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    grind
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq98
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq210 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq52 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq53 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq213 eq14
    | exact resolve eq14 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (k (M.op X0 X0) X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq55
    | exact resolve eq55 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq372 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq113
    | exact resolve eq113 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq381 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1
       have i₂ := eq55 X0 (M.op X1 X0)
       grind)
    | exact superpose eq55 eq378
    | exact resolve eq378 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq394 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq54 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq54 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X1 X1) X1 X2 X1
       have i₂ := eq55 X1 X1
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq54 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq54 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq55 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq54 X0 x x X3
       grind)
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X1
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq431
    | exact resolve eq431 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq429 X0 X1 X2 X3
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq429
    | exact resolve eq429 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq450 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq410 X0 X1 X2 X3 X4
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq410
    | exact resolve eq410 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq528 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (k (M.op X0 X0) X0) (M.op X0 (k (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op (M.op X2 X1) (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f545_10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 X0) X0))) := by
      intro X0 X1 X2
      grind
    have f545_15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f545_16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f545_18 : (k (M.op X0 X0) X0) ≠ (M.op X1 (M.op (M.op X2 X1) (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by grind
    have f545_23 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
      intro X0 X1
      first
      | (have i₁ := f545_16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
         have i₂ := f545_16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
         grind)
      | exact superpose f545_16 f545_16
      | exact resolve f545_16 f545_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f545_47 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
      intro X0
      grind
    have f545_50 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op (M.op X3 X2) (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f545_10 (M.op X0 X1) X1 X2
         have i₂ := f545_23 X0 X1
         grind)
      | exact superpose f545_23 f545_10
      | exact resolve f545_10 f545_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f545_117 : (M.op X0 (M.op X0 X0)) ≠ (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
      first
      | (have i₁ := f545_18
         have i₂ := f545_47 X0
         grind)
      | exact superpose f545_47 f545_18
      | exact resolve f545_18 f545_47
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f545_119 : False := by
      first
      | (have r₁ := f545_117
         have r₂ := f545_50 X0 X0 X1 X2
         grind)
      | exact resolve f545_117 f545_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f545_119
  have eq598 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X3 X1 X2 (k (M.op X0 X0) X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq54
    | exact resolve eq54 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq890 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 (M.op X0 X0) X0
       have i₂ := eq362 (M.op X0 X0)
       grind)
    | exact superpose eq362 eq67
    | exact resolve eq67 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq362
  have eq898 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq890
  have eq901 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq898
  have eq1003 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       have i₂ := eq436 (M.op X0 X0) x
       grind)
    | exact superpose eq436 eq14
    | exact resolve eq14 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq1003
  have eq1019 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1013 X0
       have i₂ := eq371 (M.op X0 X0)
       grind)
    | exact superpose eq371 eq1013
    | exact resolve eq1013 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1022 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  clear eq1019
  have eq1024 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1022 X0
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq1022
    | exact resolve eq1022 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1278 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq901 X0
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq901
    | exact resolve eq901 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq1676 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq376 (M.op x sF0) (M.op x sF0)
       have i₂ := eq14 (M.op x sF0) sF0 x
       grind)
    | exact superpose eq14 eq376
    | exact resolve eq376 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq1687 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1676 X0
       have i₂ := eq55 X0 sF0
       grind)
    | exact superpose eq55 eq1676
    | exact resolve eq1676 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq1806 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq1807 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq394 X0 X0 X0
       grind)
    | exact superpose eq394 eq52
    | exact resolve eq52 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1808 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0))
       have i₂ := eq394 X0 X0 X0
       grind)
    | exact superpose eq394 eq53
    | exact resolve eq53 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2126 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq1807 X0
       grind)
    | exact superpose eq1807 eq372
    | exact resolve eq372 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2362 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq1808 X0
       grind)
    | exact superpose eq1808 eq372
    | exact resolve eq372 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2387 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1808 eq375
    | exact resolve eq375 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq2399 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq375 eq2387
    | exact resolve eq2387 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq2387
  have eq5347 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f5347_10 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f5347_15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f5347_16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f5347_18 : (M.op X0 X0) ≠ (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) (M.op (M.op X0 X0) (k (M.op X0 X0) X0))) := by grind
    have f5347_23 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
      intro X0 X1
      first
      | (have i₁ := f5347_16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
         have i₂ := f5347_16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
         grind)
      | exact superpose f5347_16 f5347_16
      | exact resolve f5347_16 f5347_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5347_88 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
      intro X0
      grind
    have f5347_89 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f5347_10 (M.op X0 X1) X1 X2
         have i₂ := f5347_23 X0 X1
         grind)
      | exact superpose f5347_23 f5347_10
      | exact resolve f5347_10 f5347_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5347_174 : (M.op X0 X0) ≠ (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
      first
      | (have i₁ := f5347_18
         have i₂ := f5347_88 X0
         grind)
      | exact superpose f5347_88 f5347_18
      | exact resolve f5347_18 f5347_88
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5347_176 : False := by
      first
      | (have r₁ := f5347_174
         have r₂ := f5347_89 X0 X0 X1 X2
         grind)
      | exact resolve f5347_174 f5347_89
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f5347_176
  clear eq424
  have eq5394 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5347 X0 X1 X2
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq5347
    | exact resolve eq5347 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5347
  have eq5403 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5394 X0 X1 X2
       have i₂ := eq1024 X0
       grind)
    | exact superpose eq1024 eq5394
    | exact resolve eq5394 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq5394
  have eq5409 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5403 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq372 X0
       grind)
    | exact superpose eq372 eq5403
    | exact resolve eq5403 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq6256 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (k (M.op X0 X0) X0) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq371 X1
       grind)
    | exact superpose eq371 eq528
    | exact resolve eq528 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq6257 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6256 X0 X1
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq6256
    | exact resolve eq6256 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq6723 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) = (M.op y (M.op (M.op x y) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq442 X1 X0
       grind)
    | exact superpose eq442 eq381
    | exact resolve eq381 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq8227 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq444 X0 X1 X2 X3
       have i₂ := eq442 X0 X1
       grind)
    | exact superpose eq442 eq444
    | exact resolve eq444 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq8252 : ∀ X0 X1 X3 X4 : G, (M.op y (M.op (M.op x y) (M.op X3 X4))) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X3 X4))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8227 X3 X4 (M.op X1 (M.op X0 X0)) (M.op x (M.op X1 X1))
       have i₂ := eq394 x X1 X0
       grind)
    | exact superpose eq394 eq8227
    | exact resolve eq8227 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq8452 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op (M.op x y) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8227 (M.op X4 (M.op X3 X2)) (M.op X0 X1) X2 X3
       have i₂ := eq8227 X0 X1 (M.op X3 X2) X4
       grind)
    | exact superpose eq8227 eq8227
    | exact resolve eq8227 eq8227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8227
  have eq10855 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq545 X0 X1 X2
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq545
    | exact resolve eq545 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq10856 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10855 X0 X1 X2
       have i₂ := eq1278 X0
       grind)
    | exact superpose eq1278 eq10855
    | exact resolve eq10855 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10855
  have eq11017 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq372 X2
       have i₂ := eq10856 X2 X0 X1
       grind)
    | exact superpose eq10856 eq372
    | exact resolve eq372 eq10856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11534 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op (M.op X0 (M.op x y)) y) y) := by
    intro X0
    first
    | (have i₁ := eq2126 (M.op (M.op x sF0) y)
       have i₂ := eq11017 sF0 x y
       grind)
    | exact superpose eq11017 eq2126
    | exact resolve eq2126 eq11017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq11551 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2362 (M.op (M.op x sF4) sF3)
       have i₂ := eq11017 sF4 x sF3
       grind)
    | exact superpose eq11017 eq2362
    | exact resolve eq2362 eq11017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362 eq11017
  have eq11562 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11551 X0
       have i₂ := eq5409 (M.op X0 sF4) sF3
       grind)
    | exact superpose eq5409 eq11551
    | exact resolve eq11551 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11551
  have eq11575 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq11534 X0
       have i₂ := eq5409 (M.op X0 sF0) y
       grind)
    | exact superpose eq5409 eq11534
    | exact resolve eq11534 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11534
  have eq16754 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq450 X0 X1 X2 X3 X4
       have i₂ := eq442 X0 X1
       grind)
    | exact superpose eq442 eq450
    | exact resolve eq450 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq450
  have eq17161 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X3 (M.op x y)) X0)) (M.op (M.op y (M.op X0 (M.op X0 X0))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16754 (M.op X2 sF0) X0 X2 X3 X4
       have i₂ := eq10856 X0 sF0 X2
       grind)
    | exact superpose eq10856 eq16754
    | exact resolve eq16754 eq10856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10856 eq16754
  have eq19132 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq598 X0 X1 X2 X3
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq598
    | exact resolve eq598 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq19133 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19132 X0 X1 X2 X3
       have i₂ := eq1278 X0
       grind)
    | exact superpose eq1278 eq19132
    | exact resolve eq19132 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19132
  have eq19432 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq28 eq19133
    | (have j0 := eq19133 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq19133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19467 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq372 X3
       have i₂ := eq19133 X3 X0 X1 X2
       grind)
    | exact superpose eq19133 eq372
    | exact resolve eq372 eq19133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19478 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op (M.op X4 (M.op X4 X4)) (M.op X4 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6257 X4 X3
       have i₂ := eq19133 X3 X0 X1 X2
       grind)
    | exact superpose eq19133 eq6257
    | exact resolve eq6257 eq19133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6257 eq19133
  have eq19850 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq19432 X0 X1
       have i₂ := eq1807 sF3
       grind)
    | exact superpose eq1807 eq19432
    | exact resolve eq19432 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19432
  have eq23421 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq6723 X0 X1
       grind)
    | exact superpose eq6723 eq377
    | (have j0 := eq377 X0 X1
       grind)
    | exact resolve eq377 eq6723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq6723
  have eq23897 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) (M.op X0 X0)) ∨ (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23421 (k (M.op X0 X0) X0) (M.op x (k (M.op X0 X0) X0))
       have i₂ := eq68 X0 (k (M.op X0 X0) X0) x
       grind)
    | exact superpose eq68 eq23421
    | (have j0 := eq23421 (k (M.op X0 X0) X0) (M.op X1 (k (M.op X0 X0) X0))
       grind)
    | exact resolve eq23421 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq23951 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (M.op X0 X0)) ∨ (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23897 X0 X1
       have i₂ := eq5409 X1 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq5409 eq23897
    | (have j0 := eq23897 X0 X1
       grind)
    | exact resolve eq23897 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23897
  have eq24062 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) ∨ (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23951 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq23951
    | (have j0 := eq23951 X0 X1
       grind)
    | exact resolve eq23951 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23951
  have eq24123 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op X0 X0)) ∨ (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24062 X0 X1
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq24062
    | (have j0 := eq24062 X0 X1
       grind)
    | exact resolve eq24062 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq24157 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24123 X0 X1
       have i₂ := eq1278 X0
       grind)
    | exact superpose eq1278 eq24123
    | (have j0 := eq24123 X0 X1
       grind)
    | exact resolve eq24123 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24123
  have eq24172 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (M.op y (M.op (M.op x y) (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)))) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24157 X0 X0
       have i₂ := eq5409 X0 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq5409 eq24157
    | (have j0 := eq24157 X0 x
       grind)
    | exact resolve eq24157 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq24182 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq52 eq24172
    | (have j0 := eq24172 X0
       grind)
    | exact resolve eq24172 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24172
  have eq24189 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24182 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq24182
    | (have j0 := eq24182 X0
       grind)
    | exact resolve eq24182 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq24182
  have eq24196 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24189 X0
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq24189
    | (have j0 := eq24189 X0
       grind)
    | exact resolve eq24189 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24189
  have eq24200 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24196 X0
       have i₂ := eq1278 X0
       grind)
    | exact superpose eq1278 eq24196
    | (have j0 := eq24196 X0
       grind)
    | exact resolve eq24196 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24196
  have eq45485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq45485
    | exact resolve eq45485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45485
  have eq45497 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq45486
       have r₂ := eq29
       grind)
    | exact resolve eq45486 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45486
  have eq45520 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq45497 eq371
    | exact resolve eq371 eq45497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45497
  have eq45670 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq45520
    | exact resolve eq45520 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45520
  have eq46543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq45670 eq99
    | exact resolve eq99 eq45670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45670
  have eq46555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq46543
  have eq46558 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq46555
       have r₂ := eq29
       grind)
    | exact resolve eq46555 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46555
  have eq46665 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq46558 eq5409
    | exact resolve eq5409 eq46558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46558
  have eq46701 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq46665
    | exact resolve eq46665 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46665
  have eq46748 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq371 x
       have i₂ := eq46701
       grind)
    | exact superpose eq46701 eq371
    | exact resolve eq371 eq46701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46749 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq372 x
       have i₂ := eq46701
       grind)
    | exact superpose eq46701 eq372
    | exact resolve eq372 eq46701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46799 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq46701
       grind)
    | exact superpose eq46701 eq55
    | exact resolve eq55 eq46701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46701
  have eq46876 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46799
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq46799
    | exact resolve eq46799 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46799
  have eq46901 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq46749
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq46749
    | exact resolve eq46749 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46749
  have eq46902 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46748
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq46748
    | exact resolve eq46748 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46748
  have eq47296 : x ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq46876
  have eq47558 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq5409 y y
       have i₂ := eq46901
       grind)
    | exact superpose eq46901 eq5409
    | exact resolve eq5409 eq46901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46901
  have eq47602 : x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47558
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq47558
    | exact resolve eq47558 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47558
  have eq47629 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47602 eq11575
    | exact resolve eq11575 eq47602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11575
  have eq47631 : (M.op y x) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47602 eq1687
    | exact resolve eq1687 eq47602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq47635 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47602 eq55
    | exact resolve eq55 eq47602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47657 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47602 eq5409
    | exact resolve eq5409 eq47602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47701 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq210 eq47657
    | exact resolve eq47657 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq47657
  have eq47711 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47629
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq47629
    | exact resolve eq47629 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47629
  have eq47753 : y = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq372 y
       have i₂ := eq47711
       grind)
    | exact superpose eq47711 eq372
    | exact resolve eq372 eq47711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47711
  have eq47926 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq46902
       grind)
    | exact superpose eq46902 eq75
    | exact resolve eq75 eq46902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46902
  have eq47952 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq47926
    | exact resolve eq47926 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47926
  have eq48654 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47635 eq47631
    | exact resolve eq47631 eq47635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47631 eq47635
  have eq48721 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq48654
  have eq49641 : y = (M.op y (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47701 eq47753
    | exact resolve eq47753 eq47701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47701 eq47753
  have eq49714 : y = (M.op y (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49641
  have eq49855 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47602 eq49714
    | exact resolve eq49714 eq47602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47602 eq49714
  have eq49913 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49855
  have eq49961 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48721
       have i₂ := eq49913
       grind)
    | exact superpose eq49913 eq48721
    | exact resolve eq48721 eq49913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48721 eq49913
  have eq50015 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49961
  have eq50086 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq371 x
       have i₂ := eq50015
       grind)
    | exact superpose eq50015 eq371
    | exact resolve eq371 eq50015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq50015
  have eq50240 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50086
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq50086
    | exact resolve eq50086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50086
  have eq50509 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq50240
       grind)
    | exact superpose eq50240 eq75
    | exact resolve eq75 eq50240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50240
  have eq50533 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq50509
    | exact resolve eq50509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50509
  have eq50663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50533 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq50533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50533
  have eq50664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq50663
    | exact resolve eq50663 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50663
  have eq50677 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq50664
       have r₂ := eq29
       grind)
    | exact resolve eq50664 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50664
  have eq150556 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50677 eq372
    | exact resolve eq372 eq50677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50677
  have eq150821 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq150556
    | exact resolve eq150556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150556
  have eq152877 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq150821 eq5409
    | exact resolve eq5409 eq150821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150821
  have eq152942 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq152877
    | exact resolve eq152877 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152877
  have eq152943 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq152942
  have eq153005 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152943 eq11562
    | exact resolve eq11562 eq152943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153080 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq152943 eq19467
    | exact resolve eq19467 eq152943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152943
  have eq153090 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq153080 x x
       have i₂ := eq436 sF2 (M.op x x)
       grind)
    | exact superpose eq436 eq153080
    | exact resolve eq153080 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153080
  have eq153118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq153005
    | exact resolve eq153005 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153005
  have eq153206 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153118 eq1806
    | exact resolve eq1806 eq153118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153118
  have eq153664 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153090 eq53
    | exact resolve eq53 eq153090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153090
  have eq159093 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153664 eq153206
    | exact resolve eq153206 eq153664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153206 eq153664
  have eq159102 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq159093
  have eq159121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq159102 eq47952
    | exact resolve eq47952 eq159102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47952 eq159102
  have eq159142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq159121
  have eq159146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq159142
       have r₂ := eq47296
       grind)
    | exact resolve eq159142 eq47296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47296 eq159142
  have eq159151 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq159146
       have r₂ := eq29
       grind)
    | exact resolve eq159146 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159146
  have eq159322 : y = (M.op y (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq159151
       grind)
    | exact superpose eq159151 eq66
    | exact resolve eq66 eq159151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq159326 : y = (k x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113 y
       have i₂ := eq159151
       grind)
    | exact superpose eq159151 eq113
    | exact resolve eq113 eq159151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq159353 : y = (k (M.op y x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1278 y
       have i₂ := eq159151
       grind)
    | exact superpose eq159151 eq1278
    | exact resolve eq1278 eq159151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq159427 : y = (M.op y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24200 y
       have i₂ := eq159151
       grind)
    | exact superpose eq159151 eq24200
    | exact resolve eq24200 eq159151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24200
  have eq417285 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq159322
       have i₂ := eq159326
       grind)
    | exact superpose eq159326 eq159322
    | exact resolve eq159322 eq159326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159322 eq159326
  have eq417330 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq417285
  have eq417615 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq159353
       have i₂ := eq159427
       grind)
    | exact superpose eq159427 eq159353
    | exact resolve eq159353 eq159427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159353 eq159427
  have eq417832 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq417615
  have eq419550 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq159151
       have i₂ := eq417330
       grind)
    | exact superpose eq417330 eq159151
    | exact resolve eq159151 eq417330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159151 eq417330
  have eq419892 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq419550
  have eq420475 : x ≠ y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq417832
  have eq420514 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq420475
       have r₂ := eq419892
       grind)
    | exact resolve eq420475 eq419892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419892 eq420475
  have eq420544 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq420514
       grind)
    | exact superpose eq420514 eq75
    | exact resolve eq75 eq420514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq420514
  have eq420649 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq420544
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq420544
    | exact resolve eq420544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420544
  have eq420697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq420649 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq420649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420713 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq420697
    | exact resolve eq420697 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420697
  have eq420714 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq420713
  have eq752427 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq420714 eq372
    | exact resolve eq372 eq420714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq420714
  have eq753028 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq752427
    | exact resolve eq752427 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752427
  have eq788816 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq753028 eq5409
    | exact resolve eq5409 eq753028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753028
  have eq789036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq788816
    | exact resolve eq788816 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788816
  have eq789037 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq789036
  have eq789216 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq789037 eq11562
    | exact resolve eq11562 eq789037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11562
  have eq789390 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq789037 eq19467
    | exact resolve eq19467 eq789037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19467 eq789037
  have eq789431 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq789390 x x
       have i₂ := eq436 sF2 (M.op x x)
       grind)
    | exact superpose eq436 eq789390
    | exact resolve eq789390 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789390
  have eq789495 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq789216
    | exact resolve eq789216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789216
  have eq789646 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq789495 eq1806
    | exact resolve eq1806 eq789495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806 eq789495
  have eq790834 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq789431 eq53
    | exact resolve eq53 eq789431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq789431
  have eq806214 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq790834 eq789646
    | exact resolve eq789646 eq790834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789646 eq790834
  have eq806226 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq806214
  have eq806281 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq806226 eq420649
    | exact resolve eq420649 eq806226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420649 eq806226
  have eq806306 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq806281
  have eq806337 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq806306 eq29
    | exact resolve eq29 eq806306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq806339 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq806306 eq213
    | exact resolve eq213 eq806306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq806385 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq806306 eq2399
    | exact resolve eq2399 eq806306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq806764 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq806385
    | exact resolve eq806385 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq806385
  have eq806788 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq806306 eq806764
    | exact resolve eq806764 eq806306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806764
  have eq809493 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq17161 eq19850
    | exact resolve eq19850 eq17161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17161 eq19850
  have eq809526 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (σ x)) := by
    intro X0
    first
    | exact superpose eq806306 eq809493
    | exact resolve eq809493 eq806306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809493
  have eq810531 : (M.op (σ x) (σ x)) = (M.op y (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq809526 x
       have i₂ := eq436 sF2 x
       grind)
    | exact superpose eq436 eq809526
    | exact resolve eq809526 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809526
  have eq812328 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) := by
    first
    | exact superpose eq806788 eq52
    | exact resolve eq52 eq806788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq812353 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq806788 eq436
    | exact resolve eq436 eq806788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq841424 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19478 X0 X1 X2 X3 x
       have i₂ := eq8252 x x (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 X3)
       grind)
    | exact superpose eq8252 eq19478
    | exact resolve eq19478 eq8252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8252 eq19478
  have eq841425 : ∀ X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X2 X3)))) := by
    intro X2 X3
    first
    | exact superpose eq8452 eq841424
    | exact resolve eq841424 eq8452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8452 eq841424
  have eq844482 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq226 eq841425
    | exact resolve eq841425 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq841425
  have eq846153 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) = (M.op (M.op X0 (M.op x y)) (M.op y (σ x))) := by
    intro X0
    first
    | exact superpose eq806306 eq844482
    | exact resolve eq844482 eq806306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806306 eq844482
  have eq847162 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (M.op X0 (M.op x y)) (M.op y (σ x))) := by
    intro X0
    first
    | (have i₁ := eq846153 X0
       have i₂ := eq55 sF3 sF2
       grind)
    | exact superpose eq55 eq846153
    | exact resolve eq846153 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq846153
  have eq847858 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (M.op X0 (M.op x y)) (M.op y (σ x))) := by
    intro X0
    first
    | exact superpose eq806339 eq847162
    | exact resolve eq847162 eq806339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806339 eq847162
  have eq848210 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ x))) = (M.op (M.op X0 (M.op x y)) (M.op y (σ x))) := by
    intro X0
    first
    | (have i₁ := eq847858 X0
       have i₂ := eq1807 sF2
       grind)
    | exact superpose eq1807 eq847858
    | exact resolve eq847858 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807 eq847858
  have eq848415 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op x y)) (M.op y (σ x))) := by
    intro X0
    first
    | exact superpose eq812328 eq848210
    | exact resolve eq848210 eq812328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812328 eq848210
  have eq848859 : (M.op (M.op y (σ x)) (σ y)) = (k (σ y) (M.op (M.op y (σ x)) (σ y))) ∨ (σ y) = (M.op y (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq848415 eq23421
    | exact resolve eq23421 eq848415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23421 eq848415
  have eq848883 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op y (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq812353 eq848859
    | exact resolve eq848859 eq812353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812353 eq848859
  have eq849055 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq810531 eq848883
    | exact resolve eq848883 eq810531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810531 eq848883
  have eq855758 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq849055
  have eq856486 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq806788 eq855758
    | exact resolve eq855758 eq806788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806788 eq855758
  have eq856487 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq856486
  have eq856977 : (τ (σ x)) = (k y x) := by
    first
    | exact superpose eq856487 eq97
    | exact resolve eq97 eq856487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq856978 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq856487 eq99
    | exact resolve eq99 eq856487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq856487
  have eq857016 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq856978
       have r₂ := eq806337
       grind)
    | exact resolve eq856978 eq806337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856978
  have eq857017 : x = (k y x) := by
    first
    | exact superpose eq30 eq856977
    | exact resolve eq856977 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq856977
  have eq857231 : (k y x) = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq857016
  have eq857985 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq857231
       have i₂ := eq857017
       grind)
    | exact superpose eq857017 eq857231
    | exact resolve eq857231 eq857017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857017 eq857231
  have eq857986 : x = (M.op y y) := by grind
  clear eq857985
  have eq858586 : x = (M.op x y) := by
    first
    | (have i₁ := eq5409 y y
       have i₂ := eq857986
       grind)
    | exact superpose eq857986 eq5409
    | exact resolve eq5409 eq857986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5409 eq857986
  have eq858852 : x = (M.op x y) := by
    first
    | (have i₁ := eq858586
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq858586
    | exact resolve eq858586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq858586
  have eq859108 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq858852 eq22
    | exact resolve eq22 eq858852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq858852
  have eq859950 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq859108
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq859108
    | exact resolve eq859108 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq859108
  have eq860020 : False := by grind
  exact eq860020

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (k (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    grind
  have eq70 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq19
    | exact resolve eq19 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq85 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq23
    | exact resolve eq23 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq70
    | exact resolve eq70 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq125 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq96
    | exact resolve eq96 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq71 (M.op x (M.op x x))
       have i₂ := eq96 x x
       grind)
    | exact superpose eq96 eq71
    | exact resolve eq71 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq96 X1 X1
       grind)
    | exact superpose eq96 eq97
    | exact resolve eq97 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq142 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq135
    | exact resolve eq135 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq160 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq204 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq160 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq160
    | (have j0 := eq160 (σ X0)
       grind)
    | exact resolve eq160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq160 (τ X0)
       grind)
    | exact superpose eq160 eq18
    | (have j1 := eq160 (τ X0)
       grind)
    | exact resolve eq18 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq212 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq211 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211
    | (have j0 := eq211 X0
       grind)
    | exact resolve eq211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq218 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq134 X2 X3 X4
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq134
    | exact resolve eq134 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq138 X2 X3
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq138
    | exact resolve eq138 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 X2
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq142
    | exact resolve eq142 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq236 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X2
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq75
    | exact resolve eq75 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq134 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq134 eq9
    | exact resolve eq9 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq62 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq62 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq355 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq308 X0 X1 X2 X3 X4
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq308
    | exact resolve eq308 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq402 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq287 X0 X0 X0
       grind)
    | exact superpose eq287 eq287
    | exact resolve eq287 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X3 X2 X2
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq287
    | exact resolve eq287 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq948 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq930 X2 X3 X4
       have i₂ := eq134 X2 X0 X1
       grind)
    | exact superpose eq134 eq930
    | exact resolve eq930 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq930 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq9 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X0
       grind)
    | exact superpose eq9 eq930
    | exact resolve eq930 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1001 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq951 X0 X1 X2
       have i₂ := eq63 X0 (M.op X1 X2)
       grind)
    | exact superpose eq63 eq951
    | exact resolve eq951 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1027 : ∀ X0 X1 : G, (k (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) (k X0 (σ X1))) = (σ (M.op (k (τ X0) X1) (M.op (k (τ X0) X1) (k (τ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 (M.op (k (τ X0) X1) (k (τ X0) X1))
       have i₂ := eq71 (k (τ X0) X1)
       grind)
    | exact superpose eq71 eq21
    | exact resolve eq21 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1178 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 X0 (M.op X1 X0) X2 X3
       have i₂ := eq134 X0 X0 X1
       grind)
    | exact superpose eq134 eq77
    | exact resolve eq77 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1178 X0 X1 x x
       have i₂ := eq77 X0 X0 x x
       grind)
    | exact superpose eq77 eq1178
    | exact resolve eq1178 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1567 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X1 (M.op X2 X0) (M.op X2 (M.op X2 X2))
       have i₂ := eq125 X0 X2
       grind)
    | exact superpose eq125 eq134
    | exact resolve eq134 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq2117 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq402 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq138 X0 X2
       grind)
    | exact superpose eq138 eq402
    | exact resolve eq402 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2129 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq138 X2 X3
       have i₂ := eq402 X2 X0 X1
       grind)
    | exact superpose eq402 eq138
    | exact resolve eq138 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2275 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2117 X0 X1 X2
       have i₂ := eq63 X2 X0
       grind)
    | exact superpose eq63 eq2117
    | exact resolve eq2117 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq2323 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2275 X0 X1 X2
       have i₂ := eq63 X0 (M.op X0 X0)
       grind)
    | exact superpose eq63 eq2275
    | exact resolve eq2275 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2344 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2323 X0 X1 X2
       have i₂ := eq138 X0 X0
       grind)
    | exact superpose eq138 eq2323
    | exact resolve eq2323 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2348 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2344 X0 X1 X2
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq2344
    | exact resolve eq2344 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2344
  have eq2366 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2348 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq402 X0 x X1
       grind)
    | exact superpose eq402 eq2348
    | exact resolve eq2348 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2436 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2366 X0 X1 X2
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq2366
    | exact resolve eq2366 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2452 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2436 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2436
    | exact resolve eq2436 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2436
  have eq3073 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq168 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq168 X0 X1
       grind)
    | exact superpose eq168 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq168 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq168 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq168 X0 X1
       grind)
    | exact resolve eq13 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq3095 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3073 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq3096 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3095 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3096 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3096
    | (have j0 := eq3096 X0 X1
       grind)
    | exact resolve eq3096 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096
  have eq3103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102
  have eq3249 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X1) X0) = (M.op X3 (M.op (M.op X4 X3) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq218 (M.op X1 X1) x (M.op X1 (M.op X0 X0)) X3 X4
       have i₂ := eq287 x X1 X0
       grind)
    | exact superpose eq287 eq218
    | exact resolve eq218 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3770 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq287 x X1 X0
       grind)
    | exact superpose eq287 eq242
    | exact resolve eq242 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq3777 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq242 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq242
    | exact resolve eq242 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3798 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq242 X0 X2 (M.op X1 (M.op X2 X0)) X0
       have i₂ := eq236 (M.op X2 X0) X1 X0
       grind)
    | exact superpose eq236 eq242
    | exact resolve eq242 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq3886 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3777 X0 X1 X2 X3
       have i₂ := eq2452 X0 X3 X0
       grind)
    | exact superpose eq2452 eq3777
    | exact resolve eq3777 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3891 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3770 X0 X1
       have i₂ := eq2452 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2452 eq3770
    | exact resolve eq3770 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq4086 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3891 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq402 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq402 eq3891
    | exact resolve eq3891 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq4174 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq3891 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq3891 eq233
    | exact resolve eq233 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4198 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4174 X0 X1 X2
       have i₂ := eq2452 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2452 eq4174
    | exact resolve eq4174 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174
  have eq4241 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4086 X0 X1
       have i₂ := eq2452 X0 X1 X1
       grind)
    | exact superpose eq2452 eq4086
    | exact resolve eq4086 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq4276 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4241 X0 X1
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq4241
    | exact resolve eq4241 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq4241
  have eq4346 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4276 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq233 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq233 eq4276
    | exact resolve eq4276 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4353 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3891 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq4276 X0 X1
       grind)
    | exact superpose eq4276 eq3891
    | exact resolve eq3891 eq4276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276
  have eq4431 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4353 X0 X1
       have i₂ := eq2452 (M.op X1 X0) X0 X0
       grind)
    | exact superpose eq2452 eq4353
    | exact resolve eq4353 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4353
  have eq4471 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4431 X0 X1
       have i₂ := eq3798 X0 X0 X1
       grind)
    | exact superpose eq3798 eq4431
    | exact resolve eq4431 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4431
  have eq4678 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3891 X2 X1
       have i₂ := eq4346 X2 X1 X0
       grind)
    | (have i₁ := eq3891 X0 X1
       have i₂ := eq4346 X0 X1 X1
       grind)
    | exact superpose eq4346 eq3891
    | exact resolve eq3891 eq4346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891 eq4346
  have eq5986 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4198 X1 X3 (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0)
       have i₂ := eq233 (M.op X3 (M.op X1 X1)) X2 X0 (M.op X2 (M.op X3 (M.op X1 X1)))
       grind)
    | exact superpose eq233 eq4198
    | exact resolve eq4198 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6035 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4198 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4198 eq77
    | exact resolve eq77 eq4198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq6060 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6035 X0 X1 X2 X3
       have i₂ := eq2452 X3 X2 X2
       grind)
    | exact superpose eq2452 eq6035
    | exact resolve eq6035 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6035
  have eq8701 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5986 X2 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3 X4
       have i₂ := eq404 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq404 eq5986
    | exact resolve eq5986 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986
  have eq8752 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8701 X0 X1 X2 X3 X4
       have i₂ := eq2452 X1 X0 X0
       grind)
    | exact superpose eq2452 eq8701
    | exact resolve eq8701 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8701
  have eq8832 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8752 X0 X1 X2 X3 X4
       have i₂ := eq6060 X2 X1 X0 X1
       grind)
    | exact superpose eq6060 eq8752
    | exact resolve eq8752 eq6060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060 eq8752
  have eq10742 : ∀ X0 X1 : G, (τ (k X1 (k (σ (M.op (τ X0) (τ X0))) X0))) = (k (τ X1) (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq23
    | exact resolve eq23 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq84
  have eq10749 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq204 X0
       have i₂ := eq160 X0
       grind)
    | exact superpose eq160 eq204
    | (have j0 := eq204 X0
       have j1 := eq160 (σ X0)
       grind)
    | exact resolve eq204 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq204
  have eq11934 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2129 X4 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3 X2
       have i₂ := eq404 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq404 eq2129
    | exact resolve eq2129 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq2129
  have eq12211 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11934 X0 X1 X2 X3 X4
       have i₂ := eq8832 X0 X1 X3 X1 (M.op X0 X1)
       grind)
    | exact superpose eq8832 eq11934
    | exact resolve eq11934 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11934
  have eq12575 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq10
    | (have j1 := eq212 X0
       grind)
    | exact resolve eq10 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq20956 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3103 (M.op X0 X0) X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq3103
    | (have j0 := eq3103 (M.op X0 X0) X0
       grind)
    | exact resolve eq3103 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20961 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3103 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3103
    | (have j0 := eq3103 (τ X0) (τ X1)
       grind)
    | exact resolve eq3103 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq20978 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3103 X0 X1
       grind)
    | exact superpose eq3103 eq10
    | (have j1 := eq3103 X0 X1
       grind)
    | exact resolve eq10 eq3103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20999 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20961 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20961
    | (have j0 := eq20961 X0 X1
       grind)
    | exact resolve eq20961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20961
  have eq21016 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20999 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20999
    | (have j0 := eq20999 X0 X1
       grind)
    | exact resolve eq20999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20999
  have eq21021 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21016 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq21016
    | (have j0 := eq21016 X0 X1
       grind)
    | exact resolve eq21016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21016
  have eq21026 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21021 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21021
    | (have j0 := eq21021 X0 X1
       grind)
    | exact resolve eq21021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21021
  have eq21031 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21026 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21026
    | (have j0 := eq21026 X0 X1
       grind)
    | exact resolve eq21026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21026
  have eq21044 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3103 X0 X1
       have i₂ := eq21031 X0 X1
       grind)
    | exact superpose eq21031 eq3103
    | (have j0 := eq3103 X0 X1
       have j1 := eq21031 (σ X0) (σ X1)
       grind)
    | exact resolve eq3103 eq21031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq21097 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4471 X0 X1
       have i₂ := eq1001 X0 X1 X0
       grind)
    | exact superpose eq1001 eq4471
    | exact resolve eq4471 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471
  have eq31595 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq355 X0 X1 X2 X3 X4
       have i₂ := eq1001 X1 X0 X1
       grind)
    | exact superpose eq1001 eq355
    | exact resolve eq355 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq31608 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X1 (M.op X2 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq31595 X1 (M.op X2 X0) X3 X4 X5
       have i₂ := eq1001 X1 X2 X0
       grind)
    | exact superpose eq1001 eq31595
    | exact resolve eq31595 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31694 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X2))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31595 X3 X2 (M.op x x) (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       have i₂ := eq31595 X1 X0 x x (M.op X1 X0)
       grind)
    | exact superpose eq31595 eq31595
    | exact resolve eq31595 eq31595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31730 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 (M.op X3 X4)) (M.op (M.op X4 (M.op X3 X4)) (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op X3 X4))))) = (M.op (M.op (M.op X5 X6) (M.op X7 X7)) (M.op X7 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq31595 X1 (M.op X1 (M.op X0 X1)) X2 X3 X4
       have i₂ := eq31595 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq31595 eq31595
    | exact resolve eq31595 eq31595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31789 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))))) = (M.op (M.op (M.op X3 X4) (M.op (M.op (M.op X5 X6) (M.op X2 X2)) (M.op (M.op X5 X6) (M.op X2 X2)))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq31595 X2 (M.op X1 (M.op X0 X1)) X3 X4 (M.op (M.op X5 X6) (M.op X2 X2))
       have i₂ := eq306 X1 X0 X5 X6 X2
       grind)
    | exact superpose eq306 eq31595
    | exact resolve eq31595 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq32016 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X4 (M.op X1 X0)) (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X3 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 X3 X2 (M.op X4 (M.op X1 X0)) (M.op (M.op x x) (M.op X4 X4))
       have i₂ := eq31595 X1 X0 x x X4
       grind)
    | exact superpose eq31595 eq77
    | exact resolve eq77 eq31595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32119 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X4 (M.op X1 X0)) (M.op X0 (M.op X3 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32016 X0 X1 X2 X3 X4
       have i₂ := eq8832 X1 X0 (M.op X3 (M.op X2 X3)) X0 X0
       grind)
    | exact superpose eq8832 eq32016
    | exact resolve eq32016 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32016
  have eq32268 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31789 X0 X1 X2 x x x x
       have i₂ := eq8832 (M.op x x) (M.op X2 X2) (M.op X0 X1) (M.op x x) (M.op (M.op x x) (M.op X2 X2))
       grind)
    | exact superpose eq8832 eq31789
    | exact resolve eq31789 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31789
  have eq32321 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X5 X6) (M.op X7 X7)) (M.op X7 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op X3 X4))))) = (M.op (M.op X4 (M.op X3 X4)) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq31730 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq12211 X2 X2 X4 (M.op X3 X4) (M.op X0 X1)
       grind)
    | exact superpose eq12211 eq31730
    | exact resolve eq31730 eq12211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211 eq31730
  have eq32340 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X2))) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31694 X0 X1 X2 X3
       have i₂ := eq8832 X1 X0 (M.op (M.op X1 X0) (M.op X3 X2)) X0 X0
       grind)
    | exact superpose eq8832 eq31694
    | exact resolve eq31694 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31694
  have eq32462 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X2 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32268 X0 X1 X2
       have i₂ := eq1001 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1001 eq32268
    | exact resolve eq32268 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq32268
  have eq32499 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X3 X4) (M.op X3 X4)) = (M.op (M.op (M.op X5 X6) (M.op X7 X7)) (M.op X7 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq32321 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq1240 (M.op X3 X4) X4
       grind)
    | exact superpose eq1240 eq32321
    | exact resolve eq32321 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32321
  have eq32578 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X4 (M.op X3 X4)) = (M.op (M.op (M.op X5 X6) (M.op X7 X7)) (M.op X7 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq32499 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq2452 X4 X3 X3
       grind)
    | exact superpose eq2452 eq32499
    | exact resolve eq32499 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32499
  have eq34781 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X4 X5)) (M.op X5 (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X1 X0) X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq32119 X0 X1 X0 (M.op X0 X0) X4
       have i₂ := eq134 X0 X1 X2
       grind)
    | exact superpose eq134 eq32119
    | exact resolve eq32119 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32119
  have eq35157 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X4 X5)) (M.op X5 X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq34781 X0 X1 X2 X3 X4 X5
       have i₂ := eq233 X0 X1 X2 X2
       grind)
    | exact superpose eq233 eq34781
    | exact resolve eq34781 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34781
  have eq35482 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32340 X3 X2 X0 (M.op X1 (M.op X2 X3))
       have i₂ := eq134 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq134 eq32340
    | exact resolve eq32340 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35520 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21097 X3 X2
       have i₂ := eq32340 X0 X1 X3 X2
       grind)
    | exact superpose eq32340 eq21097
    | exact resolve eq21097 eq32340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq35611 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X4 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 (M.op X3 X4) X2 X4 X3
       have i₂ := eq32340 X0 X1 (M.op X3 X4) X2
       grind)
    | exact superpose eq32340 eq77
    | exact resolve eq77 eq32340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35964 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X2 X3) (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq35482 X0 x X2 X3
       have i₂ := eq4678 x (M.op X2 X3) X0
       grind)
    | exact superpose eq4678 eq35482
    | exact resolve eq35482 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35482
  have eq37576 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq948 X3 X2 (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) X4 X5
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq948
    | exact resolve eq948 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38274 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq37576 X0 X1 X2 X3 X4 X5
       have i₂ := eq2452 (M.op X0 X0) (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq2452 eq37576
    | exact resolve eq37576 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37576
  have eq38460 : ∀ X0 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) = (M.op (M.op X2 X3) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq38274 X0 x X2 X3 X4 X5
       have i₂ := eq4678 x (M.op X2 X3) (M.op X0 X0)
       grind)
    | exact superpose eq4678 eq38274
    | exact resolve eq38274 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38274
  have eq38539 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq38460 X0 X2 X3 X4 X5
       have i₂ := eq2452 X0 X0 X0
       grind)
    | exact superpose eq2452 eq38460
    | exact resolve eq38460 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38460
  have eq41362 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1567 X2 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) X3
       have i₂ := eq134 X0 (M.op X2 (M.op X2 X2)) X1
       grind)
    | exact superpose eq134 eq1567
    | exact resolve eq1567 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41938 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41362 X0 X1 X2 X3
       have i₂ := eq4678 (M.op X1 (M.op X2 (M.op X2 X2))) X0 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0)
       grind)
    | exact superpose eq4678 eq41362
    | exact resolve eq41362 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41362
  have eq42163 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41938 X0 X1 X2 X3
       have i₂ := eq32340 X0 (M.op X1 (M.op X2 (M.op X2 X2))) X0 (M.op X1 (M.op X2 (M.op X2 X2)))
       grind)
    | exact superpose eq32340 eq41938
    | exact resolve eq41938 eq32340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41938
  have eq42278 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X2 (M.op X2 X2)) (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq42163 X0 x X2 X3
       have i₂ := eq4678 x (M.op X2 (M.op X2 X2)) X0
       grind)
    | exact superpose eq4678 eq42163
    | exact resolve eq42163 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42163
  have eq42341 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq42278 X0 X2 X3
       have i₂ := eq3886 X0 X2 X2 X2
       grind)
    | exact superpose eq3886 eq42278
    | exact resolve eq42278 eq3886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42278
  have eq46205 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X7 X7) = (M.op X6 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op (M.op X3 (M.op X4 (M.op X5 X6))) X7)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq948 (M.op X4 (M.op X5 X6)) X3 X7 X6 X5
       have i₂ := eq35157 (M.op X5 X6) X4 (M.op (M.op X3 (M.op X4 (M.op X5 X6))) X7) X0 X1 X2
       grind)
    | exact superpose eq35157 eq948
    | exact resolve eq948 eq35157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35157
  have eq46555 : ∀ X0 X1 X2 X6 X7 : G, (M.op X7 X7) = (M.op X6 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X6 X7)))) := by
    intro X0 X1 X2 X6 X7
    first
    | (have i₁ := eq46205 X0 X1 X2 x x x X6 X7
       have i₂ := eq8832 x X6 X7 x x
       grind)
    | exact superpose eq8832 eq46205
    | exact resolve eq46205 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46205
  have eq46950 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))))) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35964 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op X2 X3))) X2 X3
       have i₂ := eq31595 (M.op X2 X3) (M.op X2 X3) X2 X3 (M.op X2 X3)
       grind)
    | exact superpose eq31595 eq35964
    | exact resolve eq35964 eq31595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31595
  have eq47157 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X3 X1) (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1567 X1 (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X3
       have i₂ := eq35964 (M.op X1 (M.op X1 X1)) X2 X0
       grind)
    | exact superpose eq35964 eq1567
    | exact resolve eq1567 eq35964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq47194 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X3 X1) (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47157 X0 X1 X2 X3
       have i₂ := eq4678 X1 (M.op X1 X1) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4678 eq47157
    | exact resolve eq47157 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47157
  have eq47332 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))))) = (M.op X1 (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46950 X0 X1 X2 X3
       have i₂ := eq8832 X0 X1 (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))))) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8832 eq46950
    | exact resolve eq46950 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46950
  have eq47401 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47194 X0 X1 X2 X3
       have i₂ := eq77 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq77 eq47194
    | exact resolve eq47194 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47194
  have eq47460 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))))) = (M.op X1 (M.op (M.op X3 X2) (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47332 X0 X1 X2 X3
       have i₂ := eq35964 (M.op X0 X1) X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq47332 X2 X3 X2 X3
       have i₂ := eq35964 (M.op X2 X3) X2 X3
       grind)
    | exact superpose eq35964 eq47332
    | exact resolve eq47332 eq35964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35964 eq47332
  have eq47489 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47401 X0 X1 X2 X3
       have i₂ := eq4678 (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))
       grind)
    | exact superpose eq4678 eq47401
    | exact resolve eq47401 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47401
  have eq47519 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47460 X2 X1 X2 X3
       have i₂ := eq9 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq9 eq47460
    | exact resolve eq47460 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47460
  have eq47532 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47489 X0 X1 X2 X3
       have i₂ := eq32340 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op X2 X0)
       grind)
    | exact superpose eq32340 eq47489
    | exact resolve eq47489 eq32340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32340 eq47489
  have eq47547 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X1 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47519 X0 X1 X2 X3
       have i₂ := eq3798 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq3798 eq47519
    | exact resolve eq47519 eq3798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798 eq47519
  have eq47556 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47532 X0 X1 X2 X3
       have i₂ := eq8832 X1 X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))))) (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact superpose eq8832 eq47532
    | exact resolve eq47532 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47532
  have eq47567 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 X1))) = (M.op X1 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47547 X0 X1 X2 X3
       have i₂ := eq2452 X1 X0 X0
       grind)
    | exact superpose eq2452 eq47547
    | exact resolve eq47547 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47547
  have eq47573 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47556 X0 X1 x X3
       have i₂ := eq4678 x X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))
       grind)
    | exact superpose eq4678 eq47556
    | exact resolve eq47556 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47556
  have eq47581 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47573 X0 X1 X3
       have i₂ := eq2452 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq2452 eq47573
    | exact resolve eq47573 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47573
  have eq47585 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47581 X0 X1 X3
       have i₂ := eq4678 X1 (M.op X1 X1) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq4678 eq47581
    | exact resolve eq47581 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47581
  have eq47588 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op (M.op X3 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47585 X0 X1 X3
       have i₂ := eq77 X1 X1 (M.op X1 X1) X1
       grind)
    | exact superpose eq77 eq47585
    | exact resolve eq47585 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq47585
  have eq50159 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op X3 X3)))))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq233 X2 X2 X3 X4
       have i₂ := eq3249 X3 X2 X0 X1
       grind)
    | exact superpose eq3249 eq233
    | exact resolve eq233 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq75359 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq47588 X5 (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) X2
       have i₂ := eq948 X3 X4 X0 X2 X1
       grind)
    | exact superpose eq948 eq47588
    | exact resolve eq47588 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq47588
  have eq75960 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq75359 X0 X1 X2 X3 X4 X5
       have i₂ := eq2452 (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X1 X2) (M.op X1 X2)
       grind)
    | exact superpose eq2452 eq75359
    | exact resolve eq75359 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75359
  have eq76105 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X3) X0)) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq75960 X0 X0 X1 X3 X4 X5
       have i₂ := eq4678 X0 X1 (M.op X3 (M.op (M.op X4 X3) X0))
       grind)
    | exact superpose eq4678 eq75960
    | exact resolve eq75960 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678 eq75960
  have eq76180 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X2 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) = (M.op (M.op X0 X0) (M.op X5 (M.op X2 (M.op (M.op (M.op X4 X3) X0) (M.op X3 (M.op (M.op X4 X3) X0)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq76105 X0 X1 X2 X1 X4 X5
       have i₂ := eq2452 (M.op (M.op X4 X1) X0) X1 X1
       grind)
    | exact superpose eq2452 eq76105
    | exact resolve eq76105 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452 eq76105
  have eq76212 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op X4 X3) X0))) (M.op X5 (M.op X2 X0))) = (M.op (M.op X0 X0) (M.op X5 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq76180 X2 X1 X2 X0 X1 X5
       have i₂ := eq233 X0 X1 X2 (M.op X1 X0)
       grind)
    | exact superpose eq233 eq76180
    | exact resolve eq76180 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq76180
  have eq76226 : ∀ X0 X2 X5 : G, (M.op (M.op X0 X0) (M.op X5 (M.op X2 X0))) = (M.op X0 (M.op X5 (M.op X2 X0))) := by
    intro X0 X2 X5
    first
    | (have i₁ := eq76212 X0 x X2 x x X5
       have i₂ := eq8832 (M.op x x) X0 (M.op X5 (M.op X2 X0)) (M.op x X2) x
       grind)
    | exact superpose eq8832 eq76212
    | exact resolve eq76212 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76212
  have eq105225 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X4 (M.op X5 (M.op X6 X4))) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 (M.op X0 X4)))) (M.op X5 (M.op X6 X4))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq76226 X4 X6 X5
       have i₂ := eq46555 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq46555 eq76226
    | exact resolve eq76226 eq46555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76226
  have eq105934 : ∀ X0 X4 X5 X6 : G, (M.op X4 (M.op X5 (M.op X6 X4))) = (M.op (M.op X0 X4) (M.op X5 (M.op X6 X4))) := by
    intro X0 X4 X5 X6
    first
    | (have i₁ := eq105225 X0 x x x X4 X5 X6
       have i₂ := eq8832 x (M.op X0 X4) (M.op X5 (M.op X6 X4)) X0 (M.op x (M.op x x))
       grind)
    | exact superpose eq8832 eq105225
    | exact resolve eq105225 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105225
  have eq106380 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq12575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575
  have eq106403 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq106380 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq106380
    | (have j0 := eq106380 (σ X0)
       grind)
    | exact resolve eq106380 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq106380
  have eq106404 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq106403 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106403
    | (have j0 := eq106403 X0
       grind)
    | exact resolve eq106403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106403
  have eq106407 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq106404 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106404
    | (have j0 := eq106404 X0
       grind)
    | exact resolve eq106404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106404
  have eq216792 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X3)) = (M.op X3 (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35611 X2 x X3 X3 X3
       have i₂ := eq38539 X3 x X2 X0 X1
       grind)
    | exact superpose eq38539 eq35611
    | exact resolve eq35611 eq38539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35611 eq38539
  have eq296833 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0)
       have i₂ := eq10749 X0
       grind)
    | exact superpose eq10749 eq71
    | (have j1 := eq10749 X0
       grind)
    | exact resolve eq71 eq10749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296834 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 (σ X0)
       have i₂ := eq10749 X0
       grind)
    | exact superpose eq10749 eq75
    | (have j1 := eq10749 X0
       grind)
    | exact resolve eq75 eq10749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10749
  have eq297128 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq296833 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq296833
    | (have j0 := eq296833 X0
       grind)
    | exact resolve eq296833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296833
  have eq297162 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq297128 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq297128
    | (have j0 := eq297128 X0
       grind)
    | exact resolve eq297128 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297128
  have eq512381 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X1 (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32462 X0 X1 X2
       have i₂ := eq47567 X2 (M.op X1 (M.op X0 X1)) X1 X0
       grind)
    | exact superpose eq47567 eq32462
    | exact resolve eq32462 eq47567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32462
  have eq512382 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq512381 X0 X1 X2
       have i₂ := eq105934 X1 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq105934 eq512381
    | exact resolve eq512381 eq105934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512381
  have eq553545 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X4 (M.op X3 X4)) = (M.op (M.op (M.op X5 X6) (M.op (M.op X2 X2) (M.op X2 X2))) (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq32578 x x X2 X3 X4 X5 X6 (M.op X2 X2)
       have i₂ := eq218 (M.op X2 X2) (M.op x x) (M.op X2 (M.op X3 X4)) X0 X1
       grind)
    | (have i₁ := eq32578 x x X2 X3 X4 X5 X6 (M.op X2 X2)
       have i₂ := eq218 X0 X1 (M.op X2 (M.op X3 X4)) (M.op X2 X2) (M.op x x)
       grind)
    | exact superpose eq218 eq32578
    | exact resolve eq32578 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq32578
  have eq556532 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X3 X4)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq553545 X0 X1 X2 X3 X4 x x
       have i₂ := eq8832 X2 X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op X3 X4)))) (M.op x x) (M.op X2 X2)
       grind)
    | exact superpose eq8832 eq553545
    | exact resolve eq553545 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8832 eq553545
  have eq567272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq21044 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21044
  have eq567379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq567272 x y
       grind)
    | exact superpose eq567272 eq16
    | (have j1 := eq567272 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq567272 x y
       grind)
    | exact resolve eq16 eq567272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567272
  have eq567775 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq567379
  have eq567915 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20978 y y
       have i₂ := eq567775
       grind)
    | exact superpose eq567775 eq20978
    | exact resolve eq20978 eq567775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20978
  have eq567919 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71 (σ y)
       have i₂ := eq567775
       grind)
    | exact superpose eq567775 eq71
    | exact resolve eq71 eq567775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568017 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1240 (σ y) (σ y)
       have i₂ := eq567775
       grind)
    | exact superpose eq567775 eq1240
    | exact resolve eq1240 eq567775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568330 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq567919
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq567919
    | exact resolve eq567919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567919
  have eq568333 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq567915
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq567915
    | exact resolve eq567915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567915
  have eq568354 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21031 eq568330
    | (have j1 := eq21031 x y
       grind)
    | exact resolve eq568330 eq21031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568330
  have eq568366 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq568017
       grind)
    | exact superpose eq568017 eq16
    | exact resolve eq16 eq568017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568017
  have eq568777 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21031 y y
       have i₂ := eq568333
       grind)
    | exact superpose eq568333 eq21031
    | (have j0 := eq21031 x y
       grind)
    | exact resolve eq21031 eq568333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21031 eq568333
  have eq568779 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq568777
  have eq569981 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20956 y
       have i₂ := eq568779
       grind)
    | exact superpose eq568779 eq20956
    | (have j0 := eq20956 y
       grind)
    | exact resolve eq20956 eq568779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570421 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq567775 eq569981
    | exact resolve eq569981 eq567775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569981
  have eq570465 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq567775 eq570421
    | exact resolve eq570421 eq567775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570421
  have eq570466 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq570465
  have eq570480 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq568779 eq570466
    | exact resolve eq570466 eq568779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568779 eq570466
  have eq570481 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq570480
  have eq570490 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq570481 eq567775
    | exact resolve eq567775 eq570481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567775
  have eq570493 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq570481 eq568354
    | exact resolve eq568354 eq570481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568354 eq570481
  have eq601528 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq570490 eq570493
    | exact resolve eq570493 eq570490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570490 eq570493
  have eq601529 : x = (M.op y y) := by
    first
    | (have r₁ := eq601528
       have r₂ := eq568366
       grind)
    | exact resolve eq601528 eq568366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568366 eq601528
  have eq601622 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq134 X0 y y
       have i₂ := eq601529
       grind)
    | exact superpose eq601529 eq134
    | exact resolve eq134 eq601529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq601627 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq234 y y X0
       have i₂ := eq601529
       grind)
    | exact superpose eq601529 eq234
    | exact resolve eq234 eq601529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq601636 : x = (M.op x y) := by
    first
    | (have i₁ := eq1240 y y
       have i₂ := eq601529
       grind)
    | exact superpose eq601529 eq1240
    | exact resolve eq1240 eq601529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq601750 : ∀ X0 X1 X2 : G, y = (M.op x (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 x))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50159 X0 X1 X2 y y
       have i₂ := eq601529
       grind)
    | exact superpose eq601529 eq50159
    | exact resolve eq50159 eq601529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50159
  have eq601909 : ∀ X0 X1 X2 : G, (M.op y x) = (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556532 X0 X1 X2 y y
       have i₂ := eq601529
       grind)
    | exact superpose eq601529 eq556532
    | exact resolve eq556532 eq601529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556532 eq601529
  have eq601914 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq601909 x x x
       have i₂ := eq35520 x x x x
       grind)
    | exact superpose eq35520 eq601909
    | exact resolve eq601909 eq35520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35520 eq601909
  have eq601919 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq601750 x x x
       have i₂ := eq216792 x x x x
       grind)
    | exact superpose eq216792 eq601750
    | exact resolve eq601750 eq216792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216792 eq601750
  have eq601940 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq601636
       grind)
    | exact superpose eq601636 eq16
    | exact resolve eq16 eq601636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601636
  have eq617629 : ∀ X0 X1 : G, (k (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) (k X0 (σ X1))) = (σ (M.op y (M.op x (k (τ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1027 X0 X1
       have i₂ := eq601622 (k (τ X0) X1)
       grind)
    | exact superpose eq601622 eq1027
    | exact resolve eq1027 eq601622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq623761 : ∀ X0 : G, (k (τ (σ (M.op (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0)))) (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))) = (τ (σ (M.op y (M.op x (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0))))) := by
    intro X0
    first
    | (have i₁ := eq10742 (σ X0) (σ (M.op (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0)))
       have i₂ := eq617629 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       grind)
    | exact superpose eq617629 eq10742
    | exact resolve eq10742 eq617629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10742 eq617629
  have eq623769 : ∀ X0 : G, (k (τ (σ (M.op (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0)))) (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))) = (M.op y (M.op x (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0))) := by
    intro X0
    first
    | (have i₁ := eq623761 X0
       have i₂ := eq10 (M.op y (M.op x (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0)))
       grind)
    | exact superpose eq10 eq623761
    | exact resolve eq623761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623761
  have eq623843 : ∀ X0 : G, (M.op y (M.op x (k (M.op (τ (σ X0)) (τ (σ X0))) X0))) = (k (τ (σ (M.op (k (M.op (τ (σ X0)) (τ (σ X0))) X0) (k (M.op (τ (σ X0)) (τ (σ X0))) X0)))) (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq623769 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq623769
    | exact resolve eq623769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623769
  have eq623908 : ∀ X0 : G, (M.op y (M.op x (k (M.op (τ (σ X0)) (τ (σ X0))) X0))) = (k (τ (σ (M.op (k (M.op (τ (σ X0)) (τ (σ X0))) X0) (k (M.op (τ (σ X0)) (τ (σ X0))) X0)))) (M.op y (M.op x (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq623843 X0
       have i₂ := eq601622 (τ (σ X0))
       grind)
    | exact superpose eq601622 eq623843
    | exact resolve eq623843 eq601622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601622 eq623843
  have eq623959 : ∀ X0 : G, (M.op y (M.op x (k (M.op X0 X0) X0))) = (k (τ (σ (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)))) (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq623908 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq623908
    | exact resolve eq623908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623908
  have eq623997 : ∀ X0 : G, (M.op y (M.op x (k (M.op X0 X0) X0))) = (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq623959 X0
       have i₂ := eq10 (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0))
       grind)
    | exact superpose eq10 eq623959
    | exact resolve eq623959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623959
  have eq624009 : ∀ X0 : G, (M.op y (M.op x (M.op X0 (M.op X0 X0)))) = (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq623997 x
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq623997
    | exact resolve eq623997 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq623997
  have eq624018 : ∀ X0 : G, (M.op y (M.op x (M.op X0 (M.op X0 X0)))) = (k (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0))) (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq624009 X0
       have i₂ := eq42341 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq42341 eq624009
    | exact resolve eq624009 eq42341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42341 eq624009
  have eq624023 : ∀ X0 : G, (k X0 (M.op y (M.op x X0))) = (M.op y (M.op x (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq624018 X0
       have i₂ := eq236 X0 X0 X0
       grind)
    | exact superpose eq236 eq624018
    | exact resolve eq624018 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq624018
  have eq624027 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq624023 X0
       have i₂ := eq601627 X0
       grind)
    | exact superpose eq601627 eq624023
    | exact resolve eq624023 eq601627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601627 eq624023
  have eq644493 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op x (M.op X0 (M.op X0 X0))))) = (M.op (M.op (M.op X1 X2) (M.op y y)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31608 (M.op X0 X0) x X0 X1 X2 y
       have i₂ := eq624027 X0
       grind)
    | exact superpose eq624027 eq31608
    | exact resolve eq31608 eq624027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31608 eq624027
  have eq645118 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op x (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq644493 X0 x x
       have i₂ := eq3886 X0 (M.op x x) y y
       grind)
    | exact superpose eq3886 eq644493
    | exact resolve eq644493 eq3886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886 eq644493
  have eq645287 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op x (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq645118 X0
       have i₂ := eq47567 x (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq47567 eq645118
    | exact resolve eq645118 eq47567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47567 eq645118
  have eq645408 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op x (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq645287 X0
       have i₂ := eq105934 X0 (M.op X0 X0) x X0
       grind)
    | exact superpose eq105934 eq645287
    | exact resolve eq645287 eq105934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105934 eq645287
  have eq645489 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq645408 X0
       have i₂ := eq512382 X0 X0 x
       grind)
    | exact superpose eq512382 eq645408
    | exact resolve eq645408 eq512382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512382 eq645408
  have eq648118 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op y x)) = (M.op X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 (M.op X0 (M.op x x))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46555 X1 X2 X3 X0 (M.op x x)
       have i₂ := eq645489 x
       grind)
    | exact superpose eq645489 eq46555
    | exact resolve eq46555 eq645489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645489
  have eq648728 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op x x)) = (M.op X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 (M.op X0 (M.op x x))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq648118 X0 X1 X2 X3
       have i₂ := eq601914
       grind)
    | exact superpose eq601914 eq648118
    | exact resolve eq648118 eq601914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601914 eq648118
  have eq649248 : ∀ X0 X1 X2 X3 : G, y = (M.op X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 (M.op X0 (M.op x x))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq648728 X0 X1 X2 X3
       have i₂ := eq601919
       grind)
    | exact superpose eq601919 eq648728
    | exact resolve eq648728 eq601919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648728
  have eq2779136 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq297162 eq296834
    | (have j0 := eq296834 X0
       have j1 := eq297162 X0
       grind)
    | exact resolve eq296834 eq297162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296834 eq297162
  have eq2781556 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2779136 x
       have i₂ := eq601919
       grind)
    | exact superpose eq601919 eq2779136
    | (have j0 := eq2779136 x
       grind)
    | exact resolve eq2779136 eq601919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601919 eq2779136
  have eq2782313 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2781556
       have r₂ := eq601940
       grind)
    | exact resolve eq2781556 eq601940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781556
  have eq2783450 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85 x
       have i₂ := eq2782313
       grind)
    | exact superpose eq2782313 eq85
    | exact resolve eq85 eq2782313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2784466 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2783450
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2783450
    | exact resolve eq2783450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783450
  have eq2784580 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2782313 eq2784466
    | exact resolve eq2784466 eq2782313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782313 eq2784466
  have eq2784625 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2784580
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2784580
    | exact resolve eq2784580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784580
  have eq2784647 : x = (M.op x x) := by
    first
    | (have j1 := eq106407 x
       grind)
    | (have r₁ := eq2784625
       have r₂ := eq106407 x
       grind)
    | exact resolve eq2784625 eq106407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106407 eq2784625
  have eq2784669 : ∀ X0 X1 X2 X3 : G, y = (M.op X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 (M.op X0 x)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq649248 X0 X1 X2 X3
       have i₂ := eq2784647
       grind)
    | exact superpose eq2784647 eq649248
    | exact resolve eq649248 eq2784647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649248
  have eq2784794 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20956 x
       have i₂ := eq2784647
       grind)
    | exact superpose eq2784647 eq20956
    | (have j0 := eq20956 x
       grind)
    | exact resolve eq20956 eq2784647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20956
  have eq2785796 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2784794
       have i₂ := eq2784647
       grind)
    | exact superpose eq2784647 eq2784794
    | exact resolve eq2784794 eq2784647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784794
  have eq2785797 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2785796
  have eq2785878 : y = (M.op x x) := by
    first
    | (have i₁ := eq2784669 x x x x
       have i₂ := eq46555 x x x x x
       grind)
    | exact superpose eq46555 eq2784669
    | exact resolve eq2784669 eq46555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46555 eq2784669
  have eq2786062 : x = y := by
    first
    | (have i₁ := eq2785878
       have i₂ := eq2784647
       grind)
    | exact superpose eq2784647 eq2785878
    | exact resolve eq2785878 eq2784647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784647 eq2785878
  have eq2786216 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq601940
       have i₂ := eq2786062
       grind)
    | exact superpose eq2786062 eq601940
    | exact resolve eq601940 eq2786062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601940 eq2786062
  have eq2786383 : False := by grind
  exact eq2786383
