import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq16 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq16 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq174 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y x
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq174
    | (have j0 := eq174 (σ y) (σ x)
       grind)
    | exact resolve eq174 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq176 eq174
    | exact resolve eq174 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq177 eq174
    | exact resolve eq174 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq175 X0 (M.op X0 X0)
       grind)
    | exact superpose eq175 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq175 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 X1) X0
       have i₂ := eq175 X1 X0
       grind)
    | exact superpose eq175 eq174
    | exact resolve eq174 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq527 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq587 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq174
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192 X1 X0
       have i₂ := eq11 (M.op X0 X0) X1
       grind)
    | exact superpose eq11 eq192
    | (have j1 := eq11 (M.op X0 X0) X1
       grind)
    | exact resolve eq192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq591 : y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq176
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq593 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq597 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq619 : y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq591
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq591 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq620 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq589 X0 X1
       have j1 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq589 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq589 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq589 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq640 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183 eq619
    | exact resolve eq619 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq641 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq661 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X1) X0
       have i₂ := eq175 X1 X0
       grind)
    | exact superpose eq175 eq12
    | (have j0 := eq12 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq175 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1
       have i₂ := eq175 X1 (M.op X1 X1)
       grind)
    | exact superpose eq175 eq661
    | (have j0 := eq661 X0 X1
       grind)
    | (have r₁ := eq661 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq175 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq661 (M.op (M.op X1 X1) (M.op X0 X0)) X1
       have r₂ := eq175 X0 (M.op X1 X1)
       grind)
    | exact resolve eq661 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq673 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq671 X0 X1
       have j1 := eq641 X1 X0
       grind)
    | (have r₁ := eq671 (k (M.op X0 X0) X1) X0
       have r₂ := eq641 X0 X1
       grind)
    | (have r₁ := eq671 X1 X0
       have r₂ := eq641 X0 X1
       grind)
    | (have r₁ := eq671 (M.op X0 X0) X1
       have r₂ := eq641 X0 (M.op X1 X1)
       grind)
    | exact resolve eq671 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq671
  have eq675 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq673 X0 X1
       have j1 := eq13 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq673 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq673 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq679 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq640 eq41
    | exact resolve eq41 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq640
  have eq680 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq679
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq679
    | exact resolve eq679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq707 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 (M.op X0 X0)
       have i₂ := eq675 x X0
       grind)
    | exact superpose eq675 eq39
    | exact resolve eq39 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq712 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq152 (M.op x x)
       have i₂ := eq675 sF3 x
       grind)
    | exact superpose eq675 eq152
    | exact resolve eq152 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq675
  have eq797 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 (M.op X1 X1)
       have i₂ := eq193 X1 (σ X0)
       grind)
    | exact superpose eq193 eq527
    | exact resolve eq527 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq527
  have eq827 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq797 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq797
    | exact resolve eq797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq839 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq598 (τ (M.op X0 X0))
       have i₂ := eq827 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq827 eq598
    | (have j0 := eq598 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq598 (τ (M.op x x))
       have r₂ := eq827 (τ (M.op x x)) x
       grind)
    | exact resolve eq598 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq827
  have eq848 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq839 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1154 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq590
       grind)
    | exact superpose eq590 eq40
    | exact resolve eq40 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1155 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1154
    | exact resolve eq1154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1157 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1155
    | exact resolve eq1155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq27509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1157 eq593
    | exact resolve eq593 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq1157
  have eq27517 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27509
       have r₂ := eq27
       grind)
    | exact resolve eq27509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27509
  have eq27556 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27517 eq848
    | exact resolve eq848 eq27517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq27517
  have eq27649 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq27556
    | exact resolve eq27556 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27556
  have eq27650 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq27649
  have eq27671 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27650 eq174
    | exact resolve eq174 eq27650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27650
  have eq27728 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27671 eq712
    | exact resolve eq712 eq27671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq27671
  have eq27828 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 (τ (σ x)) y
       grind)
    | (have r₁ := eq27728
       have r₂ := eq13 x y
       grind)
    | exact resolve eq27728 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27728
  have eq27837 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq27828
    | exact resolve eq27828 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27828
  have eq27841 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq590
       have i₂ := eq27837
       grind)
    | exact superpose eq27837 eq590
    | exact resolve eq590 eq27837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq27837
  have eq27846 : y = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq27841
  have eq27918 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 y X0
       have i₂ := eq27846
       grind)
    | exact superpose eq27846 eq175
    | exact resolve eq175 eq27846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27846
  have eq28195 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 x y
       have i₂ := eq27918 X0
       grind)
    | exact superpose eq27918 eq174
    | (have j1 := eq27918 X0
       grind)
    | exact resolve eq174 eq27918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27918
  have eq29805 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq175 x X0
       have i₂ := eq28195 X1
       grind)
    | exact superpose eq28195 eq175
    | (have j1 := eq28195 X1
       grind)
    | exact resolve eq175 eq28195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28195
  have eq31135 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq29805 X0 x
       grind)
    | exact superpose eq29805 eq18
    | (have j1 := eq29805 X0 x
       grind)
    | exact resolve eq18 eq29805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29805
  have eq31136 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31135
  have eq31242 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 x X0
       have i₂ := eq31136 X0
       grind)
    | exact superpose eq31136 eq174
    | exact resolve eq174 eq31136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq31136
  have eq32637 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31242 y
       grind)
    | exact superpose eq31242 eq18
    | (have j1 := eq31242 y
       grind)
    | exact resolve eq18 eq31242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31242
  have eq32743 : x = (M.op x y) := by grind
  clear eq32637
  have eq32783 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq32743
       grind)
    | exact superpose eq32743 eq22
    | exact resolve eq22 eq32743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq32743
  have eq32855 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32783 eq20
    | exact resolve eq20 eq32783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33126 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32855 eq680
    | exact resolve eq680 eq32855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq33763 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33126 eq587
    | (have j0 := eq587 (σ y) (σ x)
       grind)
    | exact resolve eq587 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq33126
  have eq33766 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq33763
    | exact resolve eq33763 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33763
  have eq33776 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq33766
    | exact resolve eq33766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33766
  have eq73568 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33776 eq192
    | exact resolve eq192 eq33776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq33776
  have eq76300 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73568 eq26
    | (have j1 := eq73568 (σ y)
       grind)
    | exact resolve eq26 eq73568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73568
  have eq76408 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq76300
  have eq76449 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76408 eq184
    | exact resolve eq184 eq76408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq76408
  have eq76460 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76449 eq175
    | exact resolve eq175 eq76449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq76449
  have eq76697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76460 eq26
    | (have j1 := eq76460 (σ x)
       grind)
    | exact resolve eq26 eq76460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76460
  have eq76698 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq76697
  have eq76702 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76698 eq27
    | exact resolve eq27 eq76698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76698
  have eq76717 : y = (M.op x y) := by
    first
    | (have r₁ := eq76702
       have r₂ := eq32855
       grind)
    | exact resolve eq76702 eq32855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76702
  have eq76721 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq76717
       grind)
    | exact superpose eq76717 eq24
    | exact resolve eq24 eq76717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq76725 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq76717
       grind)
    | exact superpose eq76717 eq183
    | exact resolve eq183 eq76717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq76717
  have eq76850 : (σ x) = (σ y) := by
    first
    | exact superpose eq32783 eq76721
    | exact resolve eq76721 eq32783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32783 eq76721
  have eq76866 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq76850 eq26
    | exact resolve eq26 eq76850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq76850
  have eq77168 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq76725 eq707
    | exact resolve eq707 eq76725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq76725
  have eq77267 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq77168
    | exact resolve eq77168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq77168
  have eq77309 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32855 eq77267
    | exact resolve eq77267 eq32855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77267
  have eq77456 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76866 eq11
    | exact resolve eq11 eq76866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76866
  have eq77463 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq77456
  have eq77471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77309 eq77463
    | exact resolve eq77463 eq77309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77309 eq77463
  have eq77472 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq77471
  have eq77483 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq77472 eq27
    | exact resolve eq27 eq77472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq77472
  have eq77493 : False := by grind
  exact eq77493

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 y x
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X1 X0) X0
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq61 eq59
    | exact resolve eq59 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq60 (M.op X1 X1) X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq113 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq130 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq113
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61 eq130
    | exact resolve eq130 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq137 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq136
    | exact resolve eq136 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq138 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq67 eq137
    | exact resolve eq137 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq137
  have eq352 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq526 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 (M.op X1 X1)
       have i₂ := eq89 X1 (σ X0)
       grind)
    | exact superpose eq89 eq352
    | exact resolve eq352 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq551 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq526
    | exact resolve eq526 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq597 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq59
    | (have j1 := eq69 X0 X1
       grind)
    | exact resolve eq59 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq599 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq600 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq3309 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq600 (M.op X0 X0)
       have i₂ := eq89 X0 (M.op X0 X0)
       grind)
    | exact superpose eq89 eq600
    | (have j0 := eq600 (M.op X0 X0)
       grind)
    | exact resolve eq600 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq3321 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq600 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq600
    | (have j0 := eq600 (τ X0)
       grind)
    | exact resolve eq600 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq600
  have eq3333 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq3338 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3321 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3321
    | (have j0 := eq3321 X0
       grind)
    | exact resolve eq3321 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3348 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3338 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3338
    | (have j0 := eq3338 X0
       grind)
    | exact resolve eq3338 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq6486 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq113 eq597
    | (have j0 := eq597 y (M.op x y)
       grind)
    | exact resolve eq597 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq6535 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6486
    | exact resolve eq6486 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486
  have eq6626 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6535
    | exact resolve eq6535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6713 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6626
    | exact resolve eq6626 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6626
  have eq6797 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq6713
    | exact resolve eq6713 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713
  have eq11154 : (τ (σ y)) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq138 eq135
    | exact resolve eq135 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq138
  have eq11171 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq11154
    | exact resolve eq11154 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11154
  have eq11175 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq11171
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq11171 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11171
  have eq11177 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11175 eq113
    | exact resolve eq113 eq11175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq11175
  have eq11197 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11177
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11177
    | exact resolve eq11177 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11177
  have eq19871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq19871
    | exact resolve eq19871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19871
  have eq19883 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq19872
       have r₂ := eq27
       grind)
    | exact resolve eq19872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19872
  have eq19894 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19883 eq551
    | exact resolve eq551 eq19883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq19883
  have eq19917 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq19894
    | exact resolve eq19894 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19894
  have eq19918 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq19917 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq19917 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq19917 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19917
  have eq19922 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq19918 (M.op x X0)
       grind)
    | exact superpose eq19918 eq12
    | (have j0 := eq12 X0 (σ y)
       have j1 := eq19918 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19918 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19918 X0
       grind)
    | exact resolve eq12 eq19918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19918
  have eq19924 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq19922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19922
  have eq19927 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq19924 X0
       have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq19924 X0
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq19924 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19924
  have eq20248 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq80
       have i₂ := eq19927 (k sF2 sF3)
       grind)
    | exact superpose eq19927 eq80
    | (have j1 := eq19927 X0
       grind)
    | exact resolve eq80 eq19927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq19927
  have eq20259 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq20248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20248
  have eq20267 : ∀ X0 : G, x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq20259 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq20259 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq20259 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20259
  have eq20274 : ∀ X0 : G, x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 x y
       have i₂ := eq20267 X0
       grind)
    | exact superpose eq20267 eq64
    | (have j1 := eq20267 X0
       grind)
    | exact resolve eq64 eq20267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq20267
  have eq20614 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 x
       have i₂ := eq20274 X0
       grind)
    | exact superpose eq20274 eq85
    | (have j1 := eq20274 X1
       grind)
    | exact resolve eq85 eq20274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20274
  have eq22012 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20614 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20614
    | (have j0 := eq20614 y X0
       grind)
    | exact resolve eq20614 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20614
  have eq22112 : y ≠ y ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3348 y
       have i₂ := eq22012 y
       grind)
    | exact superpose eq22012 eq3348
    | (have j0 := eq3348 y
       grind)
    | (have r₁ := eq3348 y
       have r₂ := eq22012 y
       grind)
    | exact resolve eq3348 eq22012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348 eq22012
  have eq22144 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22112
  have eq22457 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq22144
       grind)
    | exact superpose eq22144 eq60
    | exact resolve eq60 eq22144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22144
  have eq22904 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22457 x
       grind)
    | exact superpose eq22457 eq18
    | (have j1 := eq22457 x
       grind)
    | exact resolve eq18 eq22457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq22457
  have eq22905 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22904
  have eq22920 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22905 eq28
    | exact resolve eq28 eq22905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq22905
  have eq23064 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq22920
    | exact resolve eq22920 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22920
  have eq23065 : x = (M.op x y) := by grind
  clear eq23064
  have eq23066 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23065 eq20
    | exact resolve eq20 eq23065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23069 : y = (M.op y x) := by
    first
    | exact superpose eq23065 eq61
    | exact resolve eq61 eq23065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq23210 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23066
    | exact resolve eq23066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23066
  have eq23240 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23210 eq26
    | exact resolve eq26 eq23210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq23725 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23240 eq6797
    | exact resolve eq6797 eq23240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6797
  have eq23727 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11197 eq23725
    | exact resolve eq23725 eq11197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11197 eq23725
  have eq23739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23240 eq23727
    | exact resolve eq23727 eq23240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23727
  have eq23742 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23739
       have r₂ := eq27
       grind)
    | exact resolve eq23739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23739
  have eq23745 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23065 eq23742
    | exact resolve eq23742 eq23065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23065 eq23742
  have eq23750 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23745 eq85
    | exact resolve eq85 eq23745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq23745
  have eq23828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23750 eq23240
    | exact resolve eq23240 eq23750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23750
  have eq23875 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq23828
       have r₂ := eq27
       grind)
    | exact resolve eq23828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23828
  have eq23888 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23875 eq62
    | exact resolve eq62 eq23875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq23875
  have eq23904 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq23888 eq60
    | exact resolve eq60 eq23888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23888
  have eq23968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq23904 eq23240
    | exact resolve eq23240 eq23904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23904
  have eq23972 : x = y := by
    first
    | (have r₁ := eq23968
       have r₂ := eq27
       grind)
    | exact resolve eq23968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23968
  have eq23983 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq23972
       grind)
    | exact superpose eq23972 eq24
    | exact resolve eq24 eq23972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24076 : x = (M.op x x) := by
    first
    | (have i₁ := eq23069
       have i₂ := eq23972
       grind)
    | exact superpose eq23972 eq23069
    | exact resolve eq23069 eq23972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23069 eq23972
  have eq24139 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq23983
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23983
    | exact resolve eq23983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23983
  have eq24200 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23210 eq24139
    | exact resolve eq24139 eq23210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24139
  have eq24438 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24200 eq23240
    | exact resolve eq23240 eq24200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23240 eq24200
  have eq24614 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 x X0
       have i₂ := eq24076
       grind)
    | exact superpose eq24076 eq60
    | exact resolve eq60 eq24076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq24076
  have eq24751 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3333 x
       have i₂ := eq24614 x
       grind)
    | exact superpose eq24614 eq3333
    | exact resolve eq3333 eq24614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333 eq24614
  have eq24771 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24751
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24751
    | exact resolve eq24751 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24751
  have eq24783 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23210 eq24771
    | exact resolve eq24771 eq23210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23210 eq24771
  have eq24789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24438 eq24783
    | exact resolve eq24783 eq24438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24438 eq24783
  have eq24790 : False := by grind
  exact eq24790

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X1 X0) X0
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq60 (M.op X1 X1) X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq352 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq526 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 (M.op X1 X1)
       have i₂ := eq89 X1 (σ X0)
       grind)
    | exact superpose eq89 eq352
    | exact resolve eq352 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq551 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq526
    | exact resolve eq526 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq599 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq600 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq3260 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq600 (M.op X0 X0)
       have i₂ := eq89 X0 (M.op X0 X0)
       grind)
    | exact superpose eq89 eq600
    | (have j0 := eq600 (M.op X0 X0)
       grind)
    | exact resolve eq600 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq3272 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq600 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq600
    | (have j0 := eq600 (τ X0)
       grind)
    | exact resolve eq600 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq600
  have eq3284 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq3289 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3272 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3272
    | (have j0 := eq3272 X0
       grind)
    | exact resolve eq3272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3299 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3289 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3289
    | (have j0 := eq3289 X0
       grind)
    | exact resolve eq3289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq19429 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ (M.op X0 X0)) X1
       have i₂ := eq3284 X0
       grind)
    | exact superpose eq3284 eq60
    | exact resolve eq60 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19430 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ (M.op X0 X0))
       have i₂ := eq3284 X0
       grind)
    | exact superpose eq3284 eq85
    | exact resolve eq85 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq20076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq20077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq20076
    | exact resolve eq20076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20076
  have eq20088 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq20077
       have r₂ := eq27
       grind)
    | exact resolve eq20077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20077
  have eq20099 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20088 eq551
    | exact resolve eq551 eq20088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20088
  have eq20121 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq20099
    | exact resolve eq20099 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20099
  have eq20122 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq20121 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq20121 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq20121 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20121
  have eq20125 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq20122 (M.op x X0)
       grind)
    | exact superpose eq20122 eq64
    | (have j1 := eq20122 X0
       grind)
    | exact resolve eq64 eq20122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20134 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq20125 (M.op X1 X1)
       grind)
    | exact superpose eq20125 eq85
    | (have j1 := eq20125 X1
       grind)
    | exact resolve eq85 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20125
  have eq20173 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq20134
    | (have j0 := eq20134 (σ y) X0
       grind)
    | exact resolve eq20134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20134
  have eq20216 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq64 x y
       have i₂ := eq20173 X0
       grind)
    | exact superpose eq20173 eq64
    | (have j1 := eq20173 X0
       grind)
    | exact resolve eq64 eq20173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20173
  have eq20241 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19430 x X1
       have i₂ := eq20216 X0
       grind)
    | exact superpose eq20216 eq19430
    | (have j1 := eq20216 X1
       grind)
    | exact resolve eq19430 eq20216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19430 eq20216
  have eq20253 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 y) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20241 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20241
    | (have j0 := eq20241 X0 X1
       grind)
    | exact resolve eq20241 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20241
  have eq22952 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq20253 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq20253 eq26
    | (have j1 := eq20253 (σ y) X0
       grind)
    | exact resolve eq26 eq20253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20253
  have eq22986 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq22952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22952
  have eq23047 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3299 y
       have i₂ := eq22986 y
       grind)
    | exact superpose eq22986 eq3299
    | (have j0 := eq3299 y
       grind)
    | (have r₁ := eq3299 y
       have r₂ := eq22986 y
       grind)
    | exact resolve eq3299 eq22986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22986
  have eq23079 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23047
  have eq23235 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19429 y X0
       have i₂ := eq23079
       grind)
    | exact superpose eq23079 eq19429
    | exact resolve eq19429 eq23079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19429 eq23079
  have eq23249 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23235 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23235
    | (have j0 := eq23235 X0
       grind)
    | exact resolve eq23235 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23235
  have eq23809 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23249 eq26
    | (have j1 := eq23249 (σ x)
       grind)
    | exact resolve eq26 eq23249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23249
  have eq23810 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23809
  have eq23831 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23810 eq27
    | exact resolve eq27 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq23832 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq23810 eq62
    | exact resolve eq62 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq23810
  have eq23838 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq23832
       have i₂ := eq20122 (M.op sF3 sF2)
       grind)
    | exact superpose eq20122 eq23832
    | (have j1 := eq20122 X0
       grind)
    | exact resolve eq23832 eq20122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20122
  have eq46501 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq64 x y
       have i₂ := eq23838 X0
       grind)
    | exact superpose eq23838 eq64
    | (have j1 := eq23838 X0
       grind)
    | exact resolve eq64 eq23838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq23838
  have eq46513 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (k X1 y) = X1 ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 x
       have i₂ := eq46501 X0
       grind)
    | exact superpose eq46501 eq85
    | (have j1 := eq46501 X1
       grind)
    | exact resolve eq85 eq46501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq46501
  have eq46936 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq46513 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46513
    | (have j0 := eq46513 y X0
       grind)
    | exact resolve eq46513 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46513
  have eq47071 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3299 y
       have i₂ := eq46936 y
       grind)
    | exact superpose eq46936 eq3299
    | (have j0 := eq3299 y
       grind)
    | (have r₁ := eq3299 y
       have r₂ := eq46936 y
       grind)
    | exact resolve eq3299 eq46936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46936
  have eq47141 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq47071
  have eq47383 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq47141
       grind)
    | exact superpose eq47141 eq60
    | exact resolve eq60 eq47141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq47141
  have eq47785 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq47383 x
       grind)
    | exact superpose eq47383 eq18
    | (have j1 := eq47383 x
       grind)
    | exact resolve eq18 eq47383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47383
  have eq47786 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq47785
  have eq47802 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47786 eq29
    | exact resolve eq29 eq47786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq47786
  have eq47976 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq47802
    | exact resolve eq47802 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47802
  have eq47978 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq47976 eq20
    | exact resolve eq20 eq47976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47976
  have eq48218 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq47978
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47978
    | exact resolve eq47978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47978
  have eq48219 : x = y := by
    first
    | (have r₁ := eq48218
       have r₂ := eq23831
       grind)
    | exact resolve eq48218 eq23831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48218
  have eq48221 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq48219
       grind)
    | exact superpose eq48219 eq18
    | exact resolve eq18 eq48219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq48222 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq48219
       grind)
    | exact superpose eq48219 eq24
    | exact resolve eq24 eq48219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq48219
  have eq48459 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq48222
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48222
    | exact resolve eq48222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48222
  have eq48569 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq48459 eq23832
    | exact resolve eq23832 eq48459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23832 eq48459
  have eq48751 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq48569 eq551
    | exact resolve eq551 eq48569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq48569
  have eq48773 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq48751
    | exact resolve eq48751 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq48751
  have eq51328 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3299 x
       have i₂ := eq48773 x
       grind)
    | exact superpose eq48773 eq3299
    | (have j0 := eq3299 x
       grind)
    | (have r₁ := eq3299 x
       have r₂ := eq48773 x
       grind)
    | exact resolve eq3299 eq48773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3299 eq48773
  have eq51399 : x = (M.op x x) := by grind
  clear eq51328
  have eq51471 : x = (M.op x y) := by
    first
    | (have i₁ := eq51399
       have i₂ := eq48221
       grind)
    | exact superpose eq48221 eq51399
    | exact resolve eq51399 eq48221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48221 eq51399
  have eq51763 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq51471 eq20
    | exact resolve eq20 eq51471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq51471
  have eq52003 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51763
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51763
    | exact resolve eq51763 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq51763
  have eq52100 : False := by grind
  exact eq52100

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxy_pyx_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 y x
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq61 eq59
    | exact resolve eq59 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq62 eq59
    | exact resolve eq59 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq60 (M.op X1 X1) X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq93 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op y (M.op x y)) = (k y (M.op x y)) := by
    first
    | exact superpose eq67 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq67
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq96 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq68
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq97 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq96
  have eq99 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op y (M.op x y)) = (k y (M.op x y)) := by grind
  clear eq93
  have eq104 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62 eq97
    | exact resolve eq97 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : y = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61 eq99
    | exact resolve eq99 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq109 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq104
       have r₂ := eq13 x (M.op (σ x) (σ y))
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : y = (k y (M.op x y)) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq106
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq106 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq123 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq125 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq146 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq123
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq123 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq153 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq146
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq146
    | exact resolve eq146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq154 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq153
    | exact resolve eq153 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq155 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq154
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq154
    | exact resolve eq154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq175 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq111 eq125
    | exact resolve eq125 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq125
  have eq176 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq175
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq175
    | exact resolve eq175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq175
  have eq177 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq176
       have i₂ := eq11 sF3 sF1
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq300 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq423 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq424 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq553 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 (M.op X1 X1)
       have i₂ := eq87 X1 (σ X0)
       grind)
    | exact superpose eq87 eq300
    | exact resolve eq300 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq300
  have eq578 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq553
    | exact resolve eq553 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq3579 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq424 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq424
    | (have j0 := eq424 (τ X0)
       grind)
    | exact resolve eq424 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq424
  have eq3599 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3579 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3579
    | (have j0 := eq3579 X0
       grind)
    | exact resolve eq3579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3610 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3599 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3599
    | (have j0 := eq3599 X0
       grind)
    | exact resolve eq3599 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq10417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq155 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10417
    | exact resolve eq10417 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10417
  have eq10429 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10418
       have r₂ := eq27
       grind)
    | exact resolve eq10418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10418
  have eq10433 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10429
    | exact resolve eq10429 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10429
  have eq10445 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq10433 eq578
    | exact resolve eq578 eq10433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq10433
  have eq10462 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq10445
    | exact resolve eq10445 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10445
  have eq10464 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10462 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq10462 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq10462 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10462
  have eq10501 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3610 x
       have i₂ := eq10464 x
       grind)
    | exact superpose eq10464 eq3610
    | (have j0 := eq3610 x
       grind)
    | (have r₁ := eq3610 x
       have r₂ := eq10464 x
       grind)
    | exact resolve eq3610 eq10464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610 eq10464
  have eq10528 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10501
  have eq10603 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83 X0 x
       have i₂ := eq10528
       grind)
    | exact superpose eq10528 eq83
    | exact resolve eq83 eq10528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10528
  have eq11215 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10603 y
       grind)
    | exact superpose eq10603 eq18
    | (have j1 := eq10603 y
       grind)
    | exact resolve eq18 eq10603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10603
  have eq11251 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11215
  have eq11268 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11251 eq109
    | exact resolve eq109 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq11251
  have eq11534 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11268 eq155
    | exact resolve eq155 eq11268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq11268
  have eq11546 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11534
  have eq12979 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq83 X0 x
       have i₂ := eq11546
       grind)
    | exact superpose eq11546 eq83
    | exact resolve eq83 eq11546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11546
  have eq13446 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12979 y
       grind)
    | exact superpose eq12979 eq18
    | (have j1 := eq12979 y
       grind)
    | exact resolve eq18 eq12979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12979
  have eq13483 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13446
  have eq13497 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13483 eq29
    | exact resolve eq29 eq13483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13483
  have eq13603 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq13497
    | exact resolve eq13497 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13497
  have eq13752 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13603 eq61
    | exact resolve eq61 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq13603
  have eq14565 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq13752
       grind)
    | exact superpose eq13752 eq60
    | exact resolve eq60 eq13752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13752
  have eq16907 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14565 x
       grind)
    | exact superpose eq14565 eq18
    | (have j1 := eq14565 x
       grind)
    | exact resolve eq18 eq14565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14565
  have eq16908 : x = (M.op x y) := by grind
  clear eq16907
  have eq16921 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16908 eq20
    | exact resolve eq20 eq16908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16908
  have eq17013 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16921
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16921
    | exact resolve eq16921 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16921
  have eq17023 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17013 eq26
    | exact resolve eq26 eq17013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17013
  have eq19128 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17023 eq177
    | exact resolve eq177 eq17023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq19129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17023 eq19128
    | exact resolve eq19128 eq17023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19128
  have eq19130 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19129
       have r₂ := eq27
       grind)
    | exact resolve eq19129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19129
  have eq19134 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19130 eq83
    | exact resolve eq83 eq19130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq19130
  have eq19210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19134 eq17023
    | exact resolve eq17023 eq19134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19134
  have eq19257 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19210
       have r₂ := eq27
       grind)
    | exact resolve eq19210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19210
  have eq19270 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19257 eq62
    | exact resolve eq62 eq19257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq19257
  have eq19287 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq19270 eq60
    | exact resolve eq60 eq19270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq19270
  have eq20616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19287 eq17023
    | exact resolve eq17023 eq19287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17023 eq19287
  have eq20621 : False := by grind
  exact eq20621

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq124 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq130 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq131 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq776 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq138
    | exact resolve eq138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138 x y
       grind)
    | exact superpose eq138 eq16
    | (have j1 := eq138 x y
       grind)
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq809 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq776 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq776
    | (have j0 := eq776 X0 X1
       grind)
    | exact resolve eq776 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq776
  have eq1249 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq809
    | exact resolve eq809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq2043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq788
       have i₂ := eq1249 x y
       grind)
    | exact superpose eq1249 eq788
    | (have j1 := eq1249 (σ x) (σ y)
       grind)
    | (have r₁ := eq788
       have r₂ := eq1249 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq788
       have r₂ := eq1249 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq788 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq1249
  have eq2046 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2043
  have eq2048 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2046
       grind)
    | exact superpose eq2046 eq10
    | exact resolve eq10 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq2087 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2048
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2048
    | exact resolve eq2048 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2088 : x = y := by grind
  clear eq2087
  have eq2141 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2088
       grind)
    | exact superpose eq2088 eq16
    | exact resolve eq16 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2142 : False := by grind
  exact eq2142

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq42
    | (have j1 := eq83 X0 X1
       grind)
    | exact resolve eq42 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq142 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq264 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (τ X0))
       have i₂ := eq58 (τ X0) X1
       grind)
    | exact superpose eq58 eq18
    | (have j1 := eq58 (τ X0) X1
       grind)
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq58
  have eq267 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq264
    | (have j0 := eq264 X0 X1
       grind)
    | exact resolve eq264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq1889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq112
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq112
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq112
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1890 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1889
  have eq2035 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ X0) (τ X1)
       have i₂ := eq142 X1 X0
       grind)
    | exact superpose eq142 eq116
    | (have j0 := eq116 (τ X0) (τ X1)
       grind)
    | exact resolve eq116 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq142
  have eq2052 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2035
    | (have j0 := eq2035 X0 X1
       grind)
    | exact resolve eq2035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2058 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2052 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2052
    | (have j0 := eq2052 X0 X1
       grind)
    | exact resolve eq2052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2060 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2058
    | (have j0 := eq2058 X0 X1
       grind)
    | exact resolve eq2058 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2061 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2060 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2060
    | (have j0 := eq2060 X0 X1
       grind)
    | exact resolve eq2060 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq2062 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2061
    | (have j0 := eq2061 X0 X1
       grind)
    | exact resolve eq2061 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2063 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2062 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2062
    | (have j0 := eq2062 X0 X1
       grind)
    | exact resolve eq2062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq3561 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (M.op X1 X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq267
    | exact resolve eq267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq3647 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3561 X0 X1
       have i₂ := eq15 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15 eq3561
    | (have j0 := eq3561 X0 X1
       grind)
    | exact resolve eq3561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq3685 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (σ (k (M.op X1 X0) X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3647 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq3647
    | (have j0 := eq3647 X0 X1
       grind)
    | exact resolve eq3647 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq4141 : ∀ X0 X1 : G, (k X1 X0) = (M.op (k X1 X0) X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k X1 X0) X0
       have i₂ := eq2063 X1 X0
       grind)
    | exact superpose eq2063 eq42
    | (have j1 := eq2063 X1 X0
       grind)
    | exact resolve eq42 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2063
  have eq14457 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq16
    | exact resolve eq16 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq14458 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14457
       have r₂ := eq22 x
       grind)
    | exact resolve eq14457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq29890 : (σ x) = (σ (k x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3685 y x
       have i₂ := eq14458
       grind)
    | exact superpose eq14458 eq3685
    | exact resolve eq3685 eq14458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685 eq14458
  have eq29897 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq117 x y
       grind)
    | (have r₁ := eq29890
       have r₂ := eq117 x y
       grind)
    | exact resolve eq29890 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq29890
  have eq30394 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29897
       grind)
    | exact superpose eq29897 eq16
    | exact resolve eq16 eq29897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29897
  have eq30395 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq30394
       have r₂ := eq22 x
       grind)
    | exact resolve eq30394 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30394
  have eq30398 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30395
       grind)
    | exact superpose eq30395 eq16
    | exact resolve eq16 eq30395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30406 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70 (σ x) (σ y)
       have i₂ := eq30395
       grind)
    | exact superpose eq30395 eq70
    | exact resolve eq70 eq30395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq30395
  have eq30429 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq30406
  have eq30448 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq30429
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq30429
    | exact resolve eq30429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30429
  have eq30936 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30448
       grind)
    | exact superpose eq30448 eq10
    | exact resolve eq10 eq30448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30448
  have eq31029 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq30936
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30936
    | exact resolve eq30936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30936
  have eq31361 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31029
       grind)
    | exact superpose eq31029 eq16
    | exact resolve eq16 eq31029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31029
  have eq31362 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq31361
       have r₂ := eq22 x
       grind)
    | exact resolve eq31361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31361
  have eq31373 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq31362
       grind)
    | exact superpose eq31362 eq10
    | exact resolve eq10 eq31362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31362
  have eq31468 : x = (k x y) := by
    first
    | (have i₁ := eq31373
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31373
    | exact resolve eq31373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31373
  have eq31850 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4141 y x
       have i₂ := eq31468
       grind)
    | exact superpose eq31468 eq4141
    | (have j0 := eq4141 y x
       grind)
    | exact resolve eq4141 eq31468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141 eq31468
  have eq31852 : x = y ∨ x = (M.op x y) := by grind
  clear eq31850
  have eq31858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31852
       grind)
    | exact superpose eq31852 eq16
    | exact resolve eq16 eq31852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31852
  have eq31863 : x = (M.op x y) := by
    first
    | (have r₁ := eq31858
       have r₂ := eq22 x
       grind)
    | exact resolve eq31858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31858
  have eq32201 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30398
       have i₂ := eq31863
       grind)
    | exact superpose eq31863 eq30398
    | exact resolve eq30398 eq31863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30398 eq31863
  have eq32219 : (σ x) = (σ y) := by grind
  clear eq32201
  have eq32258 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq32219
       grind)
    | exact superpose eq32219 eq10
    | exact resolve eq10 eq32219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32219
  have eq32351 : x = y := by
    first
    | (have i₁ := eq32258
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32258
    | exact resolve eq32258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32258
  have eq32354 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32351
       grind)
    | exact superpose eq32351 eq16
    | exact resolve eq16 eq32351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32351
  have eq32361 : False := by grind
  exact eq32361

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq43
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq105
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq105
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1677 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1676
  have eq16061 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq16
    | exact resolve eq16 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq16062 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16061
       have r₂ := eq22 x
       grind)
    | exact resolve eq16061 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16061
  have eq43202 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45 y x
       have i₂ := eq16062
       grind)
    | exact superpose eq16062 eq45
    | exact resolve eq45 eq16062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16062
  have eq54078 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45 (σ y) (σ x)
       have i₂ := eq43202
       grind)
    | exact superpose eq43202 eq45
    | exact resolve eq45 eq43202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq43202
  have eq54082 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq54078
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq54078
    | exact resolve eq54078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54078
  have eq54870 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq54082
       grind)
    | exact superpose eq54082 eq10
    | exact resolve eq10 eq54082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54082
  have eq54972 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq54870
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq54870
    | exact resolve eq54870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54870
  have eq55682 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54972
       grind)
    | exact superpose eq54972 eq16
    | exact resolve eq16 eq54972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54972
  have eq55683 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq55682
       have r₂ := eq22 x
       grind)
    | exact resolve eq55682 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq55682
  have eq55729 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq55683
       grind)
    | exact superpose eq55683 eq10
    | exact resolve eq10 eq55683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55683
  have eq55831 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq55729
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq55729
    | exact resolve eq55729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55729
  have eq55832 : y = (M.op y y) := by grind
  clear eq55831
  have eq56752 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 y X0
       have i₂ := eq55832
       grind)
    | exact superpose eq55832 eq43
    | exact resolve eq43 eq55832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq56755 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq82 y X0
       have i₂ := eq55832
       grind)
    | exact superpose eq55832 eq82
    | exact resolve eq82 eq55832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq55832
  have eq58243 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56755 (σ x)
       grind)
    | exact superpose eq56755 eq16
    | exact resolve eq16 eq56755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56755
  have eq58292 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq58243
       have i₂ := eq56752 x
       grind)
    | exact superpose eq56752 eq58243
    | exact resolve eq58243 eq56752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56752 eq58243
  have eq58293 : False := by grind
  exact eq58293

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq110 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1145
    | exact resolve eq1145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1149 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1146
       have r₂ := eq28
       grind)
    | exact resolve eq1146 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1151 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1149
    | exact resolve eq1149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1154 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1151 eq62
    | exact resolve eq62 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1212 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1154 eq54
    | exact resolve eq54 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1277 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1212
    | (have j0 := eq1212 (σ x)
       grind)
    | exact resolve eq1212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1297 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1277 eq1151
    | exact resolve eq1151 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq1277
  have eq1303 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1297
  have eq1306 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1303 eq30
    | exact resolve eq30 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1303
  have eq1330 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1306
    | exact resolve eq1306 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1306
  have eq1331 : y = (M.op x y) ∨ x = y := by grind
  clear eq1330
  have eq1392 : y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1331 eq55
    | exact resolve eq55 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1455 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq54 y X0
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq54
    | exact resolve eq54 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1392
  have eq1598 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1455 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1455
    | (have j0 := eq1455 x
       grind)
    | exact resolve eq1455 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq1634 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1598 eq1331
    | exact resolve eq1331 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331 eq1598
  have eq1635 : x = y := by grind
  clear eq1634
  have eq1708 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1635
       grind)
    | exact superpose eq1635 eq19
    | exact resolve eq19 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1709 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1635
       grind)
    | exact superpose eq1635 eq25
    | exact resolve eq25 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1635
  have eq1734 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1709
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1709
    | exact resolve eq1709 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1709
  have eq1738 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1734 eq27
    | exact resolve eq27 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1734
  have eq1878 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1738 eq110
    | exact resolve eq110 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1738
  have eq1890 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1878
       have i₂ := eq1708
       grind)
    | exact superpose eq1708 eq1878
    | exact resolve eq1878 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708 eq1878
  have eq1893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1890 eq15
    | exact resolve eq15 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1893
    | exact resolve eq1893 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1893
  have eq1933 : False := by grind
  exact eq1933
